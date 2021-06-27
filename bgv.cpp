#include <NTL/ZZ.h>
#include <NTL/BasicThreadPool.h>
#include "FHE.h"
#include "timing.h"
#include "replicate.h"
#include "EncryptedArray.h"
#include <NTL/lzz_pXFactoring.h>

#include <cassert>
#include <cstdio>

#include <random>
#include <algorithm>
#include <fstream>
#include <cmath>
#include <time.h>
#include <chrono>
#include <omp.h>

#include <set>

using namespace std::chrono;

typedef pair<system_clock::time_point, system_clock::time_point> DUR;

const long MAX_R = 5;
long USER_NUM = 10, ITEM_NUM = 10, r_t = 100;

long calcMaxLift(long p) {
  long tl = (long)(r_t/sqrt(ITEM_NUM));
  long mx = tl * tl * ITEM_NUM * MAX_R * (USER_NUM - 1);
  cerr << "mx = " << mx << endl;
  long res = 1, tmp = p;
  while (tmp <= mx) {
    tmp *= p;
    res++;
  }
  return res;
}



// 鍵管理サーバ
class DecryptionServer {
private:
  long m, p, r, L, c, w, d;
  ZZX G;
  
  FHEcontext context;
  FHESecKey secretKey;
  const FHEPubKey& publicKey;

  const EncryptedArray *ea;
  long nSlots;

public:
  DecryptionServer(long _m, long _p, long _r, long _L, long _c, long _w, long _d) :
      m(_m), p(_p), r(_r), L(_L), c(_c), w(_w), d(_d),
        context(m, p, r), secretKey(context), publicKey(secretKey) {

    if (d == 0) {
      G = context.alMod.getFactorsOverZZ()[0];
    } else {
      G = makeIrredPoly(p, d);
    }
    buildModChain(context, L, c);
    secretKey.GenSecKey(w);
    addSome1DMatrices(secretKey);
    ea = new EncryptedArray(context, G);
    nSlots = ea->size();
  }

  const FHEPubKey& getPublicKey() {
    return publicKey;
  }

  const EncryptedArray* getEa() {
    return ea;
  }

  long getM() {
    return m;
  }

  long getNSlots() {
    return nSlots;
  }

  long calcMaxIdx(Ctxt& ct) {
    long res = 0, mx = -1;
    vector<long> pt(nSlots);
    ea->decrypt(ct, secretKey, pt);
    for (int item = 0; item < ITEM_NUM; item++) {
      if (pt[item] > mx) {
        res = item;
        mx = pt[item];
      }
    }
    return res;
  }

  long decRecommendations(Ctxt ct) {
    long index;
    index = calcMaxIdx(ct);
    return index;
  }

  vector<long> decCtxt(Ctxt& ct, long size = ITEM_NUM) {
    vector<long> pt(nSlots);
    ea->decrypt(ct, secretKey, pt);
    return pt;
  }
};


// 推薦サーバ
class RecommendationServer {
private:
  DecryptionServer *DS;
  long nSlots;

  Ctxt ctR;
  vector<Ctxt> r_sims;
  Ctxt rec;

public:
  RecommendationServer(DecryptionServer &ds):
    DS(&ds), nSlots(DS->getNSlots()), ctR(DS->getPublicKey()),
      r_sims(USER_NUM, Ctxt(DS->getPublicKey())), rec(DS->getPublicKey()) {}

  void receiveR(Ctxt ctR_) {
    ctR = ctR_;
  }

  Ctxt getR() {
    return ctR;
  }

  void receiveRsim(long ID, Ctxt r_sim) {
    r_sims[ID] = r_sim;
  }

  DUR calcRec(long target) {
    system_clock::time_point start = system_clock::now();
    
    vector<long> zeros(nSlots, 0);
    DS->getEa()->encrypt(rec, DS->getPublicKey(), zeros);
    for (long other = 0; other < USER_NUM; other++) {
      if (other == target) continue;
      rec += r_sims[other];
    }

    system_clock::time_point end = system_clock::now();
    return make_pair(start, end);
  }

  Ctxt getEncRec() {
    return rec;
  }
};



class User {
  long ID = 0;
  long recommended;

  DecryptionServer *DS;

public:
  // check用
  vector<long> rating;
  vector<long> Rating;

  Ctxt ctR;
  Ctxt r_sim;
  Ctxt ctRec;

  User(long id, DecryptionServer &ds):
    DS(&ds), ID(id), ctR(DS->getPublicKey()), r_sim(DS->getPublicKey()), ctRec(DS->getPublicKey()), 
    rating(DS->getEa()->size(),0), Rating(DS->getEa()->size(),0) {
  }

  void evaluate(long item, long r) {
    rating[item] = r;
  }

  void randomEvaluate() {
    random_device rnd;
    std::mt19937 mt(rnd());
    std::uniform_int_distribution<> randR(0, MAX_R);

    for (int item = 0; item < ITEM_NUM; item++) {
      evaluate(item, randR(mt));
    }
    calcRatings();
  }

  void calcRatings() {
    double sum = 0;
    for (int item = 0; item < ITEM_NUM; item++) {
      sum += rating[item] * rating[item];
    }
    sum = sqrt(sum);
    if (sum == 0) { sum = 1; }

    for (int item = 0; item < ITEM_NUM; item++) {
      Rating[item] = floor((double)r_t * rating[item] / sum);
    }
  }

  DUR encR() {
    system_clock::time_point start = system_clock::now();

    DS->getEa()->encrypt(ctR, DS->getPublicKey(), Rating);

    system_clock::time_point end = system_clock::now();
    return make_pair(start, end);
  }
  void sendR(RecommendationServer &RS) {
    RS.receiveR(ctR);
  }

  void receive(RecommendationServer &RS) {
    ctR = RS.getR();
  }

  DUR calcRsim() {
    system_clock::time_point start = system_clock::now();
    
    ZZX ppr, ppR;
    DS->getEa()->encode(ppr, rating);
    DS->getEa()->encode(ppR, Rating);
    r_sim = ctR;

    r_sim.multByConstant(ppR);
    totalSums(*DS->getEa(), r_sim);

    r_sim.multByConstant(ppr);
    
    system_clock::time_point end = system_clock::now();
    return make_pair(start, end);
  }

  void sendRsim(RecommendationServer &RS) {
    RS.receiveRsim(ID, r_sim);
  }

  void request(RecommendationServer &RS) {
    ctRec = RS.getEncRec();
  }

  DUR decRec() {
    system_clock::time_point start = system_clock::now();

    recommended = DS->decRecommendations(ctRec);
    
    system_clock::time_point end = system_clock::now();
    return make_pair(start, end);
  }

  long getRecommended() {
    return recommended;
  }

  void print_rating() {
    for (int item = 0; item < ITEM_NUM; item++) {
      cerr << "[" << rating[item] << "]";
    } cerr << endl;
  }

  void write_ctR(string fileName) {
    ofstream textFile(fileName, ios::trunc);
    ctR.write(textFile);
    textFile.close();
  }
  void write_rsim(string fileName) {
    ofstream textFile(fileName, ios::trunc);
    r_sim.write(textFile);
    textFile.close();
  }
  void write_ctRec(string fileName) {
    ofstream textFile(fileName, ios::trunc);
    ctRec.write(textFile);
    textFile.close();
  }

  bool correctAns(vector<long> rec) {
    vector<long> res = DS->decCtxt(ctRec);
    for (long j = 0; j < ITEM_NUM; j++) {
      if (rec[j] == res[j]) continue;
      cerr << "rec["<<j<<"] = "<<rec[j] << endl;
      cerr << "res["<<j<<"] = "<<res[j] << endl;
      return false;
    }
    return true;
  }
};



int main(int argc, char **argv) {
  ArgMapping amap;

  amap.arg("N", USER_NUM, "number of users");
  
  amap.arg("M", ITEM_NUM, "number of items");
  
  long p = 2;
  amap.arg("p", p, "plaintext base");

  long r = 1;
  amap.arg("r", r,  "lifting");
  
  long L = 0;
  amap.arg("L", L, "# of levels in the modulus chain",  "heuristic");
  
  long c = 2;
  amap.arg("c", c, "number of columns in the key-switching matrices");
  
  long w = 64;

  long d = 1;
  amap.arg("d", d, "degree of the field extension");
  amap.note("d == 0 => factors[0] defines extension");
  
  long s = 0;
  amap.arg("s", s, "minimum number of slots");

  long k = 128;
  amap.arg("k", k, "security parameter");
  
  long chosen_m = 0;
  amap.arg("m", chosen_m, "use specified value as modulus", NULL);

  long seed = 0;
  amap.arg("seed", seed, "PRG seed");

  long nt = 1;
  amap.arg("nt", nt, "num threads");

  long useOMP = 1;
  amap.arg("useOMP", useOMP, "omp or SetNumThreads");

  amap.parse(argc, argv);
  
  r = calcMaxLift(p);

  SetSeed(ZZ(seed));

  if (useOMP) {
    omp_set_num_threads(nt);
  } else {
    SetNumThreads(nt);
    omp_set_num_threads(1); 
  }

  long m = FindM(k, L, c, p, d, s, chosen_m, true);

  DecryptionServer DS(m, p, r, L, c, w, d);
  RecommendationServer RS(DS);

  // fprintf(stderr, "m, p, r, L, c, s, k, w, d, nt\n");
  fprintf(stderr, "N=%ld, M=%ld, ", USER_NUM, ITEM_NUM);
  fprintf(stderr, "m=%ld, p=%ld, r=%ld, L=%ld, c=%ld, s=%ld, k=%ld, w=%ld, d=%ld, nt=%ld\n", m, p, r, L, c, s, k, w, d, nt);
  cerr << "phi(m)     = " << phi_N(m) << endl;
  cerr << "d(=ordP)   = " << phi_N(m)/DS.getNSlots() << endl;
  cerr << "l(=nslots) = " << DS.getNSlots() << endl;

  // 時間(REAL_TIME)計測用の変数
  DUR TIME; // 型は auto で可
  // START = system_clock::now(); // 計測開始時間
  
  vector<pair<string, double> >logs;

  string ctRFileName  = "analysis/ctRCtxt2.txt";
  string RsimFileName = "analysis/simCtxt2.txt";
  string recFileName  = "analysis/recCtxt2.txt";

  vector<User> users;
  for (int id = 0; id < USER_NUM; id++) {
    User user(id, DS);
    user.randomEvaluate();
    users.push_back(user);
  }

  long ti = USER_NUM/2;
  User targetUser = users[ti];
  TIME = targetUser.encR();
  logs.push_back(make_pair("encRating ", duration_cast<milliseconds>(TIME.second-TIME.first).count()));
  targetUser.sendR(RS);

vector<long> sims(USER_NUM, 0);
vector<long> recs(ITEM_NUM, 0);

for (int other = 0; other < USER_NUM; other++) {
  if (other == ti) continue;
  for (int item = 0; item < ITEM_NUM; item++) {
    sims[other] += targetUser.Rating[item] * users[other].Rating[item];
  }
}
for (int item = 0; item < ITEM_NUM; item++) {
  for (int other = 0; other < USER_NUM; other++) {
    if (other == ti) continue;
    recs[item] += users[other].rating[item] * sims[other];
  }
}

  for (long other = 0; other < USER_NUM; other++) {
    if (other == ti) continue;
    users[other].receive(RS);
    TIME = users[other].calcRsim();
    users[other].sendRsim(RS);
    if (other == 0) {
      logs.push_back(make_pair("calcRsim  ", duration_cast<milliseconds>(TIME.second-TIME.first).count()));
    }
  }


  TIME = RS.calcRec(ti);
  logs.push_back(make_pair("calcRec   ", duration_cast<milliseconds>(TIME.second-TIME.first).count()));

  targetUser.request(RS);

  cerr << endl << "check recommendations ... ";
  if (targetUser.correctAns(recs)) {
    cerr << "OK!" << endl;
  } else {
    cerr << endl << "NG!" << endl;
  }

  TIME = targetUser.decRec();
  logs.push_back(make_pair("decRec    ", duration_cast<milliseconds>(TIME.second-TIME.first).count()));

  targetUser.write_ctR(ctRFileName);
  users[0].write_rsim(RsimFileName);
  targetUser.write_ctRec(recFileName);

  for (int i = 0; i < logs.size(); i++) {
    std::cout << logs[i].first << " ";
    printf("%.3lf\n", logs[i].second/1000);
  }
}
