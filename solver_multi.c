// Pearl PoW solver in C: keccak256(seed32 || nonce32) <= target (big-endian compare).
// Keccak-256 (pad 0x01, NOT NIST SHA3 pad 0x06). Input is exactly 64 bytes -> 1 block.
// Usage: solver SEED_HEX TARGET_HEX [seconds] [out_file]
// Uses OpenMP threads, nonce partitioned by stride. Prints FOUND nonce + digest, or rate.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdatomic.h>
#include <time.h>
#include <omp.h>

static const uint64_t RC[24] = {
 0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,0x8000000080008000ULL,
 0x000000000000808bULL,0x0000000080000001ULL,0x8000000080008081ULL,0x8000000000008009ULL,
 0x000000000000008aULL,0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,
 0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,
 0x8000000000008002ULL,0x8000000000000080ULL,0x000000000000800aULL,0x800000008000000aULL,
 0x8000000080008081ULL,0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL};
static const int ROTC[24] = {1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44};
static const int PILN[24] = {10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1};
#define ROTL(x,y) (((x) << (y)) | ((x) >> (64-(y))))

static inline void keccakf(uint64_t st[25]) {
  int i,j,round; uint64_t t, bc[5];
  for (round=0; round<24; round++) {
    for (i=0;i<5;i++) bc[i]=st[i]^st[i+5]^st[i+10]^st[i+15]^st[i+20];
    for (i=0;i<5;i++) { t = bc[(i+4)%5] ^ ROTL(bc[(i+1)%5],1); for (j=0;j<25;j+=5) st[j+i] ^= t; }
    t = st[1];
    for (i=0;i<24;i++) { j = PILN[i]; bc[0]=st[j]; st[j]=ROTL(t, ROTC[i]); t=bc[0]; }
    for (j=0;j<25;j+=5) { for (i=0;i<5;i++) bc[i]=st[j+i]; for (i=0;i<5;i++) st[j+i] ^= (~bc[(i+1)%5]) & bc[(i+2)%5]; }
    st[0] ^= RC[round];
  }
}

// digest[32] for seed||nonce
static inline void hash_nonce(const unsigned char seed[32], uint64_t nonce, unsigned char digest[32]) {
  uint64_t st[25] = {0};
  unsigned char nb[8]; int i;
  for (i=0;i<8;i++) nb[i] = (nonce >> (8*i)) & 0xff; // nonce big-endian bytes in block: last 8 bytes of 32-byte word
  // lanes 0..3 = seed (LE per lane)
  for (i=0;i<4;i++) { uint64_t v=0; int b; for (b=0;b<8;b++) v |= (uint64_t)seed[i*8+b] << (8*b); st[i]=v; }
  // lanes 4..7 = nonce as 32-byte big-endian: bytes: 24 zero bytes then nb reversed (MSB first)
  // lane4,5,6 = 0; lane7 = nonce bytes big-endian interpreted LE: byte j of lane = nonce byte (7-j)?? 
  // 32-byte word bytes: [0..23]=0, [24]=nb[7]... wait nb[i] above is little-endian byte i.
  // Word byte k (0=most significant): k<24 -> 0, k=24+j -> nonce byte (7-j) in big-endian order? nonce as integer: MSB first = byte 7 down to 0 of LE array.
  // Lane7 covers word bytes 24..31 in order, and lane LE load: lane byte b = word byte (24+b).
  // So lane7 = sum_{b=0..7} wordbyte(24+b) << (8*b), wordbyte(24+b) = (nonce >> (8*(7-b))) & 0xff.
  { uint64_t v=0; int b; for (b=0;b<8;b++) v |= (uint64_t)((nonce >> (8*(7-b))) & 0xff) << (8*b); st[7]=v; }
  // padding: byte 64 = 0x01 -> lane 8 byte 0; byte 135 = 0x80 -> lane 16 byte 7
  st[8] = 0x01ULL;
  st[16] = 0x80ULL << 56;
  keccakf(st);
  for (i=0;i<4;i++) { int b; for (b=0;b<8;b++) digest[i*8+b] = (st[i] >> (8*b)) & 0xff; }
}

static int hexval(char c){ if(c>='0'&&c<='9') return c-'0'; if(c>='a'&&c<='f') return c-'a'+10; if(c>='A'&&c<='F') return c-'A'+10; return -1; }
static int parse_hex(const char*s, unsigned char*out, int n){
  if(s[0]=='0'&&(s[1]=='x'||s[1]=='X')) s+=2;
  if((int)strlen(s)!=n*2) return -1;
  for(int i=0;i<n;i++){ int hi=hexval(s[2*i]), lo=hexval(s[2*i+1]); if(hi<0||lo<0) return -1; out[i]=(hi<<4)|lo; }
  return 0;
}

int main(int argc, char**argv){
  if(argc<3){ fprintf(stderr,"usage: %s SEED_HEX TARGET_HEX [seconds] [out]\n",argv[0]); return 1; }
  unsigned char seed[32], target[32];
  if(parse_hex(argv[1],seed,32)||parse_hex(argv[2],target,32)){ fprintf(stderr,"bad hex\n"); return 1; }
  uint64_t start_nonce = argc>=4 ? strtoull(argv[3],NULL,10) : 0;
  const char* outpath = argc>=5 ? argv[4] : NULL;
  double seconds = argc>=6 ? atof(argv[5]) : 0;
  atomic_int found_count = 0;
  double t0 = omp_get_wtime();
  uint64_t total = 0;
  #pragma omp parallel
  {
    int tid = omp_get_thread_num(); int nth = omp_get_num_threads();
    uint64_t nonce = start_nonce + (uint64_t)tid; uint64_t local=0; unsigned char dig[32];
    while(1){
      if(seconds>0 && omp_get_wtime()-t0 >= seconds) break;
      hash_nonce(seed, nonce, dig);
      local++;
      // big-endian compare dig vs target
      int le=0, gt=0;
      for(int i=0;i<32;i++){ if(dig[i]<target[i]){ le=1; break; } if(dig[i]>target[i]){ gt=1; break; } }
      if(le || (!gt && !le)){
        #pragma omp critical
        {
          FILE*f=fopen(outpath,"a");
          if(f){ fprintf(f,"nonce=%llu\nproof=", (unsigned long long)nonce); for(int i=0;i<32;i++) fprintf(f,"%02x", dig[i]); fprintf(f,"\n"); fclose(f); }
          printf("FOUND nonce=%llu proof=", (unsigned long long)nonce); for(int i=0;i<32;i++) printf("%02x", dig[i]); printf("\n"); fflush(stdout);
        }
        atomic_fetch_add(&found_count,1);
      }
      nonce += (uint64_t)nth;
      if((local & 0xFFFFF)==0 && seconds>0 && omp_get_wtime()-t0 >= seconds) break;
    }
    #pragma omp atomic
    total += local;
  }
  double elapsed = omp_get_wtime()-t0;
  printf("elapsed=%.1fs approx_hashes=%llu rate=%.0f H/s threads=%d found=%d\n", elapsed, (unsigned long long)total, total/elapsed, omp_get_max_threads(), atomic_load(&found_count));
  return 0;
}
