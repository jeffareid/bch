/*----------------------------------------------------------------------*/
/*      bch15.c         15 bit codeword, GF(2^4)                        */
/*                                                                      */
/*      Jeff Reid       2020DEC20 22:00                                 */
/*----------------------------------------------------------------------*/
#include <intrin.h>
#include <memory.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned char      BYTE;
typedef unsigned short     WORD;
typedef unsigned int       DWORD;
typedef unsigned long long QWORD;

/*                              ** GF(2^4): x^4 + x + 1 */
#define POLY (0x13)

/*                              ** GF(2^4) primitive */
#define ALPHA (0x2)

/*                              ** 3 error correction, 6 syndromes */
#define NSYN (6)

/*                              ** display euclid stuff */
#define DISPLAYE 0

typedef struct{                 /* vector structure */
    BYTE  size;
    BYTE  data[15];
}VECTOR;

typedef struct{                 /* euclid structure */
    BYTE  size;                 /* # of data bytes */
    BYTE  indx;                 /* index to right side */
    BYTE  data[NSYN+2];         /* left and right side data */
}EUCLID;

static __m128i poly;            /* generator poly */
static __m128i invpoly;         /* 2^64 / POLY */

static BYTE exp16[16];          /* exp16 table */
static BYTE log16[16];          /* log16 table */
static BYTE minplyf[32];        /* minimum polynomial flags */
static BYTE minply[16];         /* minimum polynomials */
static BYTE mincnt;             /* # of minimum polymials */

static __m128i psyn[NSYN];      /* syndrome polynomials */
static __m128i invsyn[NSYN];    /* inverse syndrome polynomials */

static __m128i msg;             /* msg.m128i_u64[0] is test message */
static __m128i par;             /* par.m128i_u64[1] is parities */

static QWORD   encmsg;          /* copy of encoded message */

static EUCLID   E0;             /* used by GenpErrorsE */
static EUCLID   E1;

static VECTOR   vSyndromes;
static VECTOR   pErrors;
static VECTOR   pLambda;
static VECTOR   vLocators;
static VECTOR   vOffsets;

static void Tbli(void);
static void GenPoly(void);
static void Encode(void);
static void GenSyndromes(void);
static void GenpErrorsE(void);
static void GenOffsets(void);
static void FixErrors(void);
static int  Poly2Root(VECTOR *, VECTOR *);
static BYTE GFPwr(BYTE, BYTE);
static BYTE GFMpy(BYTE, BYTE);
static BYTE GFDiv(BYTE, BYTE);
static void ShowEuclid(EUCLID *);
static void ShowVector(VECTOR *);

#define GFAdd(a, b) (a^b)
#define GFSub(a, b) (a^b)

main()
{
    Tbli();                     /* init tables */
    GenPoly();                  /* generate poly info */
    msg.m128i_u64[0] = 0x5c00ull;   /* test message */
    Encode();                   /* encode message */
    encmsg = msg.m128i_u64[0];
    msg.m128i_u64[0] ^= 0x34ull;    /* create error(s) */
    GenSyndromes();             /* generate syndromes */
    GenpErrorsE();              /* generate error location info */
    GenOffsets();               /* convert to offsets */
    FixErrors();                /* correct error bits */
    if(encmsg == msg.m128i_u64[0])
        printf("passed\n");
    else
        printf("failed\n");
    return 0;
}

/*----------------------------------------------------------------------*/
/*      Tbli                                                            */
/*----------------------------------------------------------------------*/
static void Tbli()              /* init tables */
{
__m128i d0, alpha;
BYTE *p0, *p1;
    alpha.m128i_u64[0] = ALPHA; /* init exp16 table */
    d0.m128i_u64[0] = 0x01;
    p0 = exp16;
    for(p1 = p0+16; p0 < p1;){
        *p0++ = d0.m128i_u8[0];
        d0 = _mm_clmulepi64_si128(d0, alpha, 0x00);
        if(d0.m128i_u8[0] & 0x40)
            d0.m128i_u8[0] ^= POLY<<2;
        if(d0.m128i_u8[0] & 0x20)
            d0.m128i_u8[0] ^= POLY<<1;
        if(d0.m128i_u8[0] & 0x10)
            d0.m128i_u8[0] ^= POLY<<0;
    }
    p0 = exp16;                 /* init log16 table */
    p1 = log16;
    *p1 = 0;
    for(d0.m128i_u8[0] = 0; d0.m128i_u8[0] < 15; d0.m128i_u8[0] += 1)
        *(p1+*p0++) = d0.m128i_u8[0];
}

/*----------------------------------------------------------------------*/
/*      GenPoly                                                         */
/*----------------------------------------------------------------------*/
static void GenPoly(void)
{
QWORD M;
QWORD N;
QWORD Q;
DWORD x;
BYTE mpoly;                     /* test polynomial */
BYTE sum;                       /* sum, looking for zeroes */
BYTE apwr;                      /* alpha to power */
BYTE i,j;

    /* find minimum and non-duplicate polynomials for m[1] -> m[NSYN] */
    i = 0;
    do{
        apwr = GFPwr(ALPHA,++i);
        for(mpoly = 0x02; mpoly <= 0x1f ; mpoly++){
            sum = 0;
            for(j = 0; j <= 4; j++){
                if(mpoly&(1<<j))
                    sum ^= GFPwr(apwr,j);
            }
            if(sum == 0){
                if(minplyf[mpoly] != 0)
                    continue;
                minplyf[mpoly] = 1;
                minply[mincnt] = mpoly;
                mincnt += 1;
                break;
            }
        }
    }while(i < NSYN);

    poly.m128i_u64[0] = minply[0];
    for(i = 1; i < mincnt; i++){
        poly.m128i_u64[1] = minply[i];
        poly = _mm_clmulepi64_si128(poly, poly, 0x01);
    }

    /* generate inverse of encoding polynomial */
    _BitScanReverse64(&x, poly.m128i_u64[0]);
    M = 1ull<<x;
    N = M>>1;
    Q = 0x0ull;
    for(i = 0; i < 65-x; i++){
        N <<= 1;
        Q <<= 1;
        if(N&M){
            Q |= 1;
            N ^= (poly.m128i_u64[0]);
        }
    }
    invpoly.m128i_u64[0] = Q;
}

/*----------------------------------------------------------------------*/
/*      Encode                                                          */
/*----------------------------------------------------------------------*/
static void Encode(void)
{
    par = _mm_clmulepi64_si128(msg, invpoly, 0x00); /* par[1] = quotient */
    par = _mm_clmulepi64_si128(par, poly, 0x01);    /* par[0] = product */
    par.m128i_u64[0] ^= msg.m128i_u64[0];           /* par[0] = remainder */
    msg.m128i_u64[0] |= par.m128i_u64[0];           /* msg[0] = encoded message */
}

/*----------------------------------------------------------------------*/
/*      GenSyndromes                                                    */
/*----------------------------------------------------------------------*/
static void GenSyndromes(void)
{
QWORD M;
DWORD x;
BYTE i, ap, s;
    vSyndromes.size = NSYN;
    for(i = 0; i < NSYN; i++){
        M = msg.m128i_u64[0];
        ap = GFPwr(ALPHA, i+1);
        s = 0;
        while(M){
            _BitScanReverse64(&x, M);
            M ^= 1ull<<x;
            s ^= GFPwr(ap, x);
        }
        vSyndromes.data[i] = s;
    }       
}

/*----------------------------------------------------------------------*/
/*      GenpErrorsE     generate pErrors via Euclid division algorithm  */
/*----------------------------------------------------------------------*/
static void GenpErrorsE(void)
{
/* R[] is msb first | A[] is msb last (reversed) */
EUCLID *pED;                            /* R[i-2] | A[i-1] */
EUCLID *pER;                            /* R[i-1] | A[i-2] */
EUCLID *pET;                            /* temp */
int     i, j;
BYTE    bME;                            /* max errors possible */
BYTE    bQuot;                          /* quotient */

/*      E0 = initial ED: E0.R[-1] = x^MAXERR, E0.A[0] = 1 */
    E0.size = vSyndromes.size+2;
    E0.indx = vSyndromes.size+1;
    E0.data[0] = 1;
    memset(&E0.data[1], 0, vSyndromes.size*sizeof(BYTE));
    E0.data[E0.indx] = 1;
    pED = &E0;

/*      E1 = initial ER: E1.R[0] = syndrome polynomial, E1.A[-1] = 0 */
    E1.size = vSyndromes.size+2;
    E1.indx = vSyndromes.size+1;
    E1.data[0] = 0;
    for(i = 1; i < E1.indx; i++){
        E1.data[i] = vSyndromes.data[vSyndromes.size-i];}
    E1.data[E1.indx] = 0;
    pER = &E1;

/*      init bME */
    bME = vSyndromes.size/2;

/*      Euclid algorithm */

    while(1){                           /* while degree ER.R > max errors */ 
#if DISPLAYE
        printf("ED: ");
        ShowEuclid(pED);
        printf("ER: ");
        ShowEuclid(pER);
#endif
        while((pER->data[0] == 0) &&    /* shift dvsr left until msb!=0 */
              (pER->indx != 0)){        /*  or fully shifted left */
            pER->indx--;
            memcpy(&pER->data[0], &pER->data[1], (pER->size-1)*sizeof(BYTE));
            pER->data[pER->size-1] = 0;}

        if(pER->indx <= bME){           /* if degree ER.R[] <= bME, break */
            break;}

        while(1){                       /* while more sub-steps */
            if(pED->data[0]){           /*   if ED.R[] msb!=0, update ED, ER */
                bQuot = GFDiv(pED->data[0], pER->data[0]); /* Q=ED.R[msb]/ER.R[msb] */
                for(i = 0; i < pER->indx; i++){            /* ED.R[]=ED.R[]-Q*ER.R[] */
                    pED->data[i] = GFSub(pED->data[i], GFMpy(bQuot, pER->data[i]));}
                for(i = pED->indx; i < pER->size; i++){    /* ER.A[]=ER.A[]-Q*ED.A[] */
                    pER->data[i] = GFSub(pER->data[i], GFMpy(bQuot, pED->data[i]));}}
            if(pED->indx == pER->indx){ /*   if sub-steps done, break */
                break;}
            pED->indx--;                /*   shift ED left */
            memcpy(&pED->data[0], &pED->data[1], (pED->size-1)*sizeof(BYTE));
            pED->data[pED->size-1] = 0;}

        pET = pER;                      /* swap ED, ER */
        pER = pED;
        pED = pET;}

    pErrors.size = pED->size-pED->indx; /* set pErrors.size */

    if((pER->indx) >= pErrors.size){    /*  if degree ER.R too high */
        printf("GenpErrorsE remainder.size >= errors.size\n");
        goto fail0;}

#if 0
    j = pErrors.size - 1;       /* right shift ER if Omega has leading zeroes */
    while(pER->indx < j){
        pER->indx++;
        for(i = pER->size-1; i;){
            i--;
            pER->data[i+1] = pER->data[i];}
        pER->data[0] = 0;}
#if DISPLAYE
    printf("EX: ");
    ShowEuclid(pER);
#endif
#endif

/*      pErrors = ED.A[] without unreversing = Lambda reversed */
    j = pED->indx;
    for(i = 0; i < pErrors.size; i++){
        pErrors.data[i] = pED->data[j];
        j++;}

#if DISPLAYE
    printf("pErrors (e):    ");
    ShowVector(&pErrors);
#endif

/*      Make most significant coef pErrors == 1 (divide by it) */
    bQuot = pErrors.data[0];
    if(bQuot == 0){
        printf("GenpErrorsE most sig coef of pErrors == 0\n");
        pLambda.size = 1;
        pLambda.data[0] = 1;
        goto fail0;}
    for(i = 0; i < pErrors.size; i++){
        pErrors.data[i] = GFDiv(pErrors.data[i], bQuot);}
#if DISPLAYE
    printf("pErrors (E):    ");
    ShowVector(&pErrors);
#endif

/*      Find roots of pErrors (if fail, then set for no roots) */

    if(Poly2Root(&vLocators, &pErrors)){    /* solve error poly */
        printf("GenpErrorsE poly2root failed \n");
fail0:
        pErrors.size = 1;                   /* handle no root case */
        pErrors.data[0] = 1;
        vLocators.size = 0;}
}

/*----------------------------------------------------------------------*/
/*      GenOffsets                                                      */
/*----------------------------------------------------------------------*/
static void GenOffsets(void)
{
BYTE i;
    vOffsets.size = vLocators.size;
    for(i = 0; i < vLocators.size; i++){
        vOffsets.data[i] = log16[vLocators.data[i]];
    }
}

/*----------------------------------------------------------------------*/
/*      FixErrors                                                       */
/*----------------------------------------------------------------------*/
static void FixErrors()
{
BYTE i;
    for(i = 0; i < vOffsets.size; i++)
        msg.m128i_u64[0] ^= 1ull<<vOffsets.data[i]; 
}

/*----------------------------------------------------------------------*/
/*      Poly2Root(pVDst, pPSrc)         find roots of poly              */
/*----------------------------------------------------------------------*/
static int Poly2Root(VECTOR *pVDst, VECTOR *pPSrc)
{
BYTE    bLcr;                           /* current locator */
BYTE    bSum;                           /* current sum */
BYTE    bV;                             /* index to pVDst */
BYTE    i,j;

    pVDst->size = pPSrc->size-1;        /* set dest size */

    if(!pVDst->size)                    /* exit if null */
        return(0);

    bV   = 0;
    bLcr = 1;
    for(j = 0; j < 15;  j++){
        bSum = 0;                       /* sum up terms */
        for(i = 0; i < pPSrc->size; i++){
            bSum = GFMpy(bSum, bLcr);
            bSum = GFAdd(bSum, pPSrc->data[i]);}

        if(!bSum){                      /* if a root */
            if(bV == pVDst->size){      /*    exit if too many roots */
                return(1);}
            pVDst->data[bV] = bLcr;     /*    add locator */
            bV++;}

        bLcr = GFMpy(bLcr, ALPHA);}     /* set up next higher alpha */

    if(bV != pVDst->size)               /* exit if not enough roots */
        return(1);

    return(0);
}

/*----------------------------------------------------------------------*/
/*      GFPwr                                                           */
/*----------------------------------------------------------------------*/
static BYTE GFPwr(BYTE m0, BYTE m1)
{
    return exp16[(BYTE)((log16[m0]*(DWORD)m1)%15)];
}

/*----------------------------------------------------------------------*/
/*      GFMpy                                                           */
/*----------------------------------------------------------------------*/
static BYTE GFMpy(BYTE m0, BYTE m1) /* multiply */
{
int m2;
    if(0 == m0 || 0 == m1)
        return(0);
    m2 = log16[m0] + log16[m1];
    if(m2 > 15)
        m2 -= 15;
    return(exp16[m2]);
}

/*----------------------------------------------------------------------*/
/*      GFDiv                                                           */
/*----------------------------------------------------------------------*/
static BYTE GFDiv(BYTE m0, BYTE m1) /* divide */
{
    int m2;
    if(0 == m0)
        return(0);
    m2 = log16[m0] - log16[m1];
    if(m2 < 0)
        m2 += 15;
    return(exp16[m2]);
}

/*----------------------------------------------------------------------*/
/*      ShowEuclid                                                      */
/*----------------------------------------------------------------------*/
static void ShowEuclid(EUCLID *pESrc)
{
BYTE    i;
    for(i = 0; i < pESrc->indx; i++){
        printf(" %02x", pESrc->data[i]);}
    printf("|");
    for( ; i < pESrc->size; i++){
        printf("%02x ", pESrc->data[i]);}
    printf("\n");
}

/*----------------------------------------------------------------------*/
/*      ShowVector                                                      */
/*----------------------------------------------------------------------*/
static void ShowVector(VECTOR *pVSrc)
{
BYTE    i;
    for(i = 0; i < pVSrc->size; ){
        printf(" %02x", pVSrc->data[i]);
        i++;
        if(0 == (i&0xf)){
            printf("\n");}}
    printf("\n");
}
