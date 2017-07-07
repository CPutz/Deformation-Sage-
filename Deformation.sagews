︠759096fc-1fa0-43ad-88f5-dcbfddc08accs︠
from sage.rings.polynomial.polydict import ETuple

class Family:
    global mat_valuation
    global prod
    global riseFac
    global changeCoefRing
    global transpose
    global binarySearch
    global num0
    global trunc

    def __init__(self, P, n, l, p):
        self.n = n
        self.l = l
        self.p = p
        Zt   = PolynomialRing(ZZ, 't', l)
        Ztx  = PolynomialRing(Zt, 'x', n+1)
        Zt.inject_variables()
        Ztx.inject_variables()
        self.P = Ztx(P)
        self.varsx = Ztx.gens()
        self.varst = Zt.gens()
        Zx  = PolynomialRing(ZZ, 'x', n+1)
        Zxt = PolynomialRing(Zx, 't', l)
        PPr = sum([c * Zxt(m) for (c, m) in zip(P.coefficients(), P.monomials())])
        dPdtPr = [PPr.derivative(v) for v in self.varst]
        self.dPdt = [sum([Ztx(c) * Ztx(m) for (c, m) in zip(f.coefficients(), f.monomials())]) for f in dPdtPr]
        #Compute constants and bases
        self.d = P.degree()
        self.ordPnfac = sum([floor(n/p^i) for i in range(1,log(n)/log(p) + 1)]); #Compute ord_p(n!)
        self.ordPnm1fac = 0
        if (n > 1):
            self.ordPnm1fac = sum([floor((n-1)/p^i) for i in range(1,log(n-1)/log(p) + 1)]) #Compute ord_p((n-1)!)
        self.delta = self.ordPnm1fac + sum([floor(log(i)/log(p)) for i in range(1,n)]) #Compute delta = ord_p((n-1)!) + sum_{i=1}^{n-1} floor(log_p(i))
        self.bs = self.Bs()
        self.b = len(self.bs)
        self.monListTup = sorted([x for x in Tuples(range(self.d), n+1) if sum(x) == self.d-1])
        self.dPdxTup = [[Zt(P.derivative(v).coefficient(x)) for x in self.monListTup] for v in self.varsx]
        self.Css    = [self.Cs(k)    for k in range(n+2)]
        self.Bks    = [self.B(k)     for k in range(n+2)]
        self.Rtups  = [self.Rtup(k)  for k in range(n+2)]
        self.Btups  = [self.Btup(k)  for k in range(n+2)]
        self.Ftups  = [self.Ftup(k)  for k in range(n+2)]
        self.Cstups = [self.Cstup(k) for k in range(n+2)]

    #De Rham basis
    def F(self,  k):  return [self.expToMon(e) for e in self.Ftup(k)]
    def B(self,  k):  return [self.expToMon(e) for e in self.Btup(k)]
    def Bs(self):     return [self.expToMon(e) for e in self.Bstup()]
    def R(self,  k):  return [self.expToMon(e) for e in self.Rtup(k)]
    def Cs(self, k):  return [(j, self.expToMon(e)) for (j, e) in self.Cstup(k)]

    #De Rham basis in tuples
    def Ftup(s, k): return sorted([x for x in Tuples(range(k*s.d - s.n), s.n+1) if sum(x) == k*s.d - (s.n+1)])
    def Btup(s, k): return sorted([x for x in Tuples(range(s.d-1),       s.n+1) if sum(x) == k*s.d - (s.n+1)])
    def Bstup(s):   return [x for k in range(1,s.n+1) for x in s.Btup(k)]
    def Rtup(s, k): return [x for x in s.Ftup(k) if x not in s.Btup(k)]
    def Ctup(s, k, j):
        if j == 0:
            return sorted([x for x in Tuples(range((k-1)*s.d - s.n+1), s.n+1) if sum(x) == (k-1)*s.d - s.n])
        else:
            return [x for x in s.Ctup(k, j-1) if x[j-1] < s.d-1]
    def Cstup(s, k): return [(j, x) for j in range(s.n+1) for x in s.Ctup(k, j)]
    def DeltaTup(self, k, K):
        def comp(i, kPr):
            f = self.Rtups[k][i]
            (j, g) = self.Cstups[k][kPr]
            diff = [x - y for (x, y) in zip(f, g)]
            i = binarySearch(self.monListTup, diff)
            if (i != -1):
                return self.dPdxTup[j][i]
            else:
                return 0
        m = len(self.Css[k])
        return matrix(K, [[comp(i, kPr) for kPr in range(m)] for i in range(m)])
    def Deltas(self, K):
        return [DeltaTup(k, K) for k in range(self.n+2)]
    def binarySearch(alist, item):
        first = 0
        last = len(alist)-1
        found = False
        while first<=last and not found:
            midpoint = (first + last)//2
            if alist[midpoint] == item:
                found = True
            else:
                if item < alist[midpoint]:
                    last = midpoint-1
                else:
                    first = midpoint+1
        return midpoint if found else -1
    def expToMon(self, v): return prod([x^e for (x,e) in zip(self.varsx, v)])

    #Connection matrix
    def Decompose(self, dPdx, Q, K, Kx,):
        k = (Q.degree() + self.n + 1)//self.d
        w = vector(K, [Q.coefficient(x) for x in self.Rtups[k]])
        v = self.DeltaInverses[k] * w
        Qs = [sum([vg * Kx(g) for ((j, g), vg) in zip(self.Css[k], v) if i == j]) for i in range(self.n+1)]
        gk = Q - sum([Qs[i] * Kx(dPdx[i]) for i in range(self.n+1)])
        return (Qs, gk)

    def in_span(self, Q): return all([x in self.bs for x in Q.monomials()])
    def Reduce(self, dPdx, Q, K, Kx):
        k = (Q.degree() + self.n + 1)//self.d
        gs = [Kx(0)] * self.n
        while (k > self.n):
            (Qs, dummy) = self.Decompose(dPdx, Q, K, Kx)
            k -= 1
            Q = k^(-1) * sum([Kx(Qs[i]).derivative(self.varsx[i]) for i in range(self.n+1)])
        while not self.in_span(Q):
            (Qs, gs[k-1]) = self.Decompose(dPdx, Q, K, Kx)
            k -= 1
            Q = k^(-1) * sum([Kx(Qs[i]).derivative(self.varsx[i]) for i in range(self.n+1)])
        if Q != 0:
            gs[k-1] = Q
            k -= 1
        for i in range(1,k+1):
            gs[i-1] = Kx(0)
        return gs

    def GMConnectionQQ(self):
        Qt = FractionField(PolynomialRing(QQ, 't', self.l))
        Qt.inject_variables()
        Qtx = PolynomialRing(Qt, 'x', self.n+1)
        dPdx = [Qtx(self.P).derivative(xi) for xi in self.varsx]
        print "Computing Delta_i^(-1) for i = 1.." + `n+1`
        self.DeltaInverses = [self.DeltaTup(k, Qt).inverse() for k in range(self.n+2)]
        Ms = []
        for dPdtk in self.dPdt:
            M = matrix(Qt, self.b, self.b, 0)
            for i in range(self.b):
                print("Connection matrix row: " + `i`)
                g = self.bs[i]
                k = (g.degree() + self.n + 1)//self.d
                Q = Qtx(-k * g * dPdtk)
                gs = self.Reduce(dPdx, Q, Qt, Qtx)
                for j in range(self.b):
                    f = self.bs[j]
                    l = (f.degree() + self.n + 1)//self.d
                    if (gs[l-1].degree() > 0):
                        M[j, i] = gs[l-1].coefficient(Qtx(f)).constant_coefficient()
                    else:
                        if (f.degree() > 0):
                            M[j, i] = 0
                        else:
                            M[j, i] = gs[l-1].constant_coefficient()
                    M[j,i].reduce()
            Ms.append(M)
        return Ms

    #Frobenius
    def DiagFrob(self, P0):
        self.NAp0Pr = self.NAp0 + self.n - 1 + self.ordPnfac + 2 * self.delta
        M = ceil(self.p^2/(self.p-1) * (self.NAp0Pr + log(self.NAp0Pr + 3) / log(self.p) + 4)) - 1
        R = floor(M / self.p)
        QpNAp0   = Qp(self.p, self.NAp0)
        QpNAp0Pr = Qp(self.p, self.NAp0Pr)
        Ap0 = matrix(QpNAp0, self.b, self.b, 0)
        ai = [QpNAp0Pr(a) for a in P0.coefficients()]
        for i in range(self.b):
            print "Diagfrob row: " + `i`
            u = self.bs[i].exponents()[0]
            v = map(lambda ui: (self.p*(ui+1) - 1) % self.d ,u)
            ku = self.expToK(u)
            kv = self.expToK(v)
            f0 = lambda k    : ZZ(ai[k])^((self.p * (u[k] + 1) - (v[k] + 1)) / self.d);
            f1 = lambda k,  r: riseFac((u[k]+1)/self.d, r)
            f2 = lambda k,m,r: sum([(self.p * ZZ(ai[k])^(self.p-1))^(r-j) / (factorial(m-self.p*j) * factorial(j)) for j in xrange(r+1)])
            alphauv = prod([f0(k) * sum([f1(k, r) * f2(k, (self.p * (u[k] + 1) - (v[k] + 1)) / self.d + r*self.p, r) for r in xrange(R+1)]) for k in xrange(self.n+1)])
            ji = self.bs.index(self.expToMon(v))
            Ap0[i, ji] = (-1)^kv * factorial(kv - 1) / factorial(ku - 1) * self.p^(self.n - ku) * alphauv^(-1)
        return Ap0

    def prod(iterable):
        return reduce(operator.mul, iterable, 1)
    def lcm(iterable):
        return reduce(lcm, iterable, 1)
    def riseFac(l, r):
        return prod(map(lambda j: l + j, xrange(r)))
    def expToK(self, u):
        return (sum(u) + (self.n+1))/self.d
    def changeCoefRing(Q,R):
        return sum([R(a) * m for (a,m) in zip(Q.coefficients(), Q.monomials())])
    def transpose(x):
        return map(list, zip(*x))
    def num0(l):
        if not l or l[0] != 0:
            return 0
        else:
            return num0(l[1:]) + 1
    def trunc(f, K):
        dict = f.dict()
        return { k : dict[k] for k in dict if sum(k) < K }

    def FrobSeriesExpansion(self):
        f = (2 * self.delta + (self.n - 1));
        self.NM = self.NAp + (2 * f + 1) * ceil(log(self.K - 1) / log(self.p)) + 1
        self.NAp0 = self.NAp + f * (ceil(log(self.K - 1) / log(self.p)) + ceil(log(ceil(self.K/self.p) - 1) / log(self.p)))
        self.NC = self.NAp + f * ceil(log(self.K - 1) / log(self.p)) + self.delta
        self.NCinv = self.NAp + f * ceil(log(ceil(self.K/self.p) - 1) / log(self.p)) + self.delta
        self.NCpr = self.NC + (2 * f + 1) * ceil(log(ceil(self.K/self.p) - 1) / log(self.p))
        self.NCinvpr = self.NCinv + (2 * f + 1) * ceil(log(self.K - 1) / log(self.p))

        print "NM = " + `self.NM`
        print "NAp0 = " + `self.NAp0`
        print "NC' = " + `self.NCpr`
        print "NCinv' = " + `self.NCinvpr`

        ZptNM    = PolynomialRing(Zp(self.p, self.NM), 't', self.l)
        QpNAp0  = Qp(self.p, self.NAp0)
        ZpNC     = Zp(self.p, self.NCpr)
        ZptNC    = PolynomialRing(ZpNC, 't', self.l)
        MZpNC    = MatrixSpace(ZpNC, self.b, self.b)
        ZpNCinv  = Zp(self.p, self.NCinvpr)
        ZptNCinv = PolynomialRing(ZpNCinv, 't', self.l)
        MZpNCinv = MatrixSpace(ZpNCinv, self.b, self.b)

        Qt = PolynomialRing(QQ, 't', self.l)
        MQt = MatrixSpace(Qt, self.b, self.b)

        P0 = PolynomialRing(QpNAp0, 'x', self.n+1)(sum([a(self.l * [0]) * m for (a,m) in zip(self.P.coefficients(), self.P.monomials())]))
        Ap0 = self.DiagFrob(P0).transpose()

        rss = [Qt(r).dict() for r in self.rs]

        Gss = []
        print "computing G^(k) for k = 1.." + `self.l`
        for (M, r) in zip(self.Ms, self.rs):
            GPr = r * M
            for i in range(self.b):
                for j in range(self.b):
                    GPr[i, j].reduce()
            G = MQt(GPr)
            ms = map(lambda e: ETuple(e), set.union(*[set(x.dict().keys()) for x in G.list()]))
            Gs = map(matrix, transpose(map(transpose, [[[x.coefficient(list(e)) for e in ms] for x in sublist] for sublist in G])))
            Gss.append(zip(ms, Gs))

        zero = ETuple(self.l * [0])
        zero_matrix = matrix.zero(self.b, self.b)
        rs_zero = [r[zero] for r in rss]
        for i in range(self.l):
            del rss[i][zero]

        print "computing C_i"
        A = matrix.identity(self.b,QQ)
        Ci = {zero: matrix.identity(self.b, QQ)}
        tups = Tuples(range(self.K), self.l)
        for (index, e) in enumerate(tups):
            i = ETuple(e)
            if i != zero:
                if index % (tups.cardinality() // 10) == 0:
                    print `(100 * index) // tups.cardinality()` + "%"
                k = num0(e)
                ek = zero.eadd_p(1, k)
                C = -1/(rs_zero[k] * i[k]) * (sum([G * Ci.get(i.esub(j).esub(ek), zero_matrix) for (j, G) in Gss[k]]) + sum([(i[k] - j[k]) * rss[k][j] * Ci.get(i.esub(j), zero_matrix) for j in rss[k]]))
                Ci[i] = C
                ti = Qt({i : 1})
                A += C * ti

        self.Ci = Ci

        print "computing C_i^(-1)"
        Ainv = matrix.identity(self.b,QQ)
        Ciinv = {zero: matrix.identity(self.b, QQ)}
        Gsts = [[(j, -Gi.transpose()) for (j, Gi) in Gss[k]] for k in range(self.l)]
        tups = Tuples(range(ceil(self.K/self.p)), self.l)
        for (index, e) in enumerate(tups):
            i = ETuple(e)
            if i != zero:
                if tups.cardinality() // 10 != 0:
                    if index % (tups.cardinality() // 10) == 0:
                        print `(100 * index) // tups.cardinality()` + "%"
                k = num0(e)
                ek = zero.eadd_p(1, k)
                Cinv = -1/(rs_zero[k] * i[k]) * (sum([Gt * Ciinv.get(i.esub(j).esub(ek), zero_matrix) for (j, Gt) in Gsts[k]]) + sum([(i[k] - j[k]) * rss[k][j] * Ciinv.get(i.esub(j), zero_matrix) for j in rss[k]]))
                Ciinv[i] = Cinv
                ti = Qt({i : 1})
                Ainv += Cinv * ti^self.p

        self.A1 = A
        self.A2 = Ainv

        print "Computing Ap"
        ZptNAp = PolynomialRing(Zp(self.p, self.NAp, 'capped-rel'), 't', self.l)
        MZptNAp = MatrixSpace(ZptNAp, self.b, self.b)
        QptNAp = PolynomialRing(Qp(self.p, self.NAp, 'capped-rel'), 't', self.l)
        MQptNAp = MatrixSpace(QptNAp, self.b, self.b)
        Ap = MQptNAp(A).apply_map(lambda x: QptNAp(trunc(x, self.K))) * Ap0 * MQptNAp(Ainv.transpose()).apply_map(lambda x: QptNAp(trunc(x, self.K)))
        return MQptNAp(Ap).apply_map(lambda x: QptNAp(trunc(x, self.K)))

    def mat_valuation(M, p):
        vals = [valuation(x, p) for x in M.list() if x != 0];
        if not vals:
            return +Infinity;
        else:
            return min(vals);

    def ZetaFunction(self, tau, a = 1):
        if a == 1:
            self.NApPr = self.NAp + (a + self.b - 3) * self.delta
            ZpNApPr      = Zp(self.p, self.NApPr, 'capped-abs')
            ZpTNApPr.<T> = ZpNApPr[]
            MZpTNApPr    = MatrixSpace(ZpTNApPr, self.b, self.b)

            ZpNApDelta   = Zp(self.p, self.NAp + self.delta, 'capped-abs')
            ZptNApDelta  = PolynomialRing(ZpNApDelta, 't', self.l)
            MZptNApDelta = MatrixSpace(ZptNApDelta, self.b, self.b)

            QpNApDelta    = Qp(self.p, self.NAp + self.delta, 'capped-rel')
            QptNApDelta  = PolynomialRing(QpNApDelta, 't', self.l)
            MQptNApDelta = MatrixSpace(QptNApDelta, self.b, self.b)

            if (self.l == 1):
                tau_hat = ZpNApDelta.teichmuller(tau)
            else:
                tau_hat = map(lambda t: ZpNApDelta.teichmuller(t), tau)
            if (GF(p)(self.s(tau_hat)) != 0):
                Ap_tau = self.s(tau_hat)^(-1) * MQptNApDelta(self.s * self.Ap).apply_map(lambda x: QptNApDelta(trunc(x, self.K))(tau_hat))
                Chi = det(matrix.identity(self.b, ZpTNApPr) - T * MZpTNApPr(Ap_tau))
                Chii = Chi.padded_list(self.b+1)
                self.NChii = [floor(log(2 * (self.b/i) * self.p^(i * (self.n-1) / 2)) / log(self.p)) + 1 for i in range(1,self.b+1)]
                ChiiCapped = []
                for i in range(1,self.b+1):
                    ZpNChiiAbs = Zp(self.p, self.NChii[i-1], 'capped-abs')
                    ChiiCapped.append(ZpNChiiAbs(Chii[i]))
                print "ChiiCapped = " + `ChiiCapped`
                print "NChii = " + `self.NChii`
                ChiZj = [1]
                sj = []
                for j in range(1,self.b+1):
                    sm = sum([sj[j-i-1] * ChiZj[i] for i in range(1,j)])
                    s = -sm - j * ZZ(ChiiCapped[j-1])
                    pNChii = self.p^self.NChii[j-1]
                    k = ZZ(s) // (j * ZZ(pNChii))
                    x = s - k * j * pNChii
                    if abs(x) < abs(x - j * pNChii):
                        sj.append(x)
                    else:
                        sj.append(x - j * pNChii)
                    ChiZj.append((-sj[j-1] - sm) / j)
                print ChiZj;
                ZZT.<T> = ZZ[];
                ChiZZ = sum([x * T^i for (i,x) in enumerate(ChiZj)])
                denom = prod([1 - self.p^i * T for i in range(self.n)])
                return ChiZZ^((-1)^self.n) / denom
            else:
                print "r vanishes at fibre"
        else:
            return NotImplemented

    def Precompute(self, a=1):
        self.NChii = [floor(log(2 * (self.b/i) * self.p^(i * a * (self.n-1) / 2)) / log(self.p)) + 1 for i in range(1,self.b+1)]
        self.NAp = max(self.NChii) + self.delta #Theorem 6.14
        self.Ms = self.GMConnectionQQ()
        print "Computing r"
        self.rs = [M.denominator() for M in self.Ms]
        if (self.l == 1):
            self.r = self.rs[0]
        else:
            self.r = lcm(*self.rs)
        m = floor(1.1 * self.p * self.NAp)
        self.K = (self.r.degree() + 1) * m
        print "Computing s"
        ZptNApDelta = PolynomialRing(Zp(self.p, self.NAp + self.delta, 'capped-rel'), 't', self.l)
        Zt = PolynomialRing(ZZ, 't', self.l)
        self.s = ZptNApDelta(Zt(ZptNApDelta(self.r))^m)
        print "NAp = " + `self.NAp`
        print "K = " + `self.K`
        self.Ap = self.FrobSeriesExpansion()
︡db21a19e-0079-46ff-a75c-db95f75bede0︡{"done":true}︡
︠08a885ce-4639-41e7-a5f9-2099a08c6cdds︠
n = 2
l = 1 #number of parameters
p = 7
Zt   = PolynomialRing(ZZ, 't', l)
Ztx  = PolynomialRing(Zt, 'x', n+1)
Zt.inject_variables()
Ztx.inject_variables()
#P = x0^3 + x1^3 + x2^3 + t0*x0^2*x1 + t1*x0*x1*x2
P = x0^4 + x1^4 + x2^4 + t*x0^2*x1^2
family = Family(P, n, l, p)
︡e0ded63e-eab0-4e92-bc2b-f1bc7a879cf8︡{"stdout":"Defining t\n"}︡{"stdout":"Defining x0, x1, x2\n"}︡{"stdout":"Defining t\nDefining x0, x1, x2\n"}︡{"done":true}︡
︠3eca19d8-3b4e-4d20-abd1-b8baa2e45ee3s︠
%time
family.Precompute()
︡8abe9f23-eafa-4c48-bf82-a073b7fd76bb︡{"stdout":"Defining t\nComputing Delta_i^(-1) for i = 1..3\nConnection matrix row: 0"}︡{"stdout":"\nConnection matrix row: 1\nConnection matrix row: 2\nConnection matrix row: 3\nConnection matrix row: 4\nConnection matrix row: 5"}︡{"stdout":"\nComputing r\nComputing s\nNAp = 4\nK = 90\nNM = 14\nNAp0 = 9\nNC' = 13\nNCinv' = 15\nDiagfrob row: 0\nDiagfrob row: 1\nDiagfrob row: 2"}︡{"stdout":"\nDiagfrob row: 3\nDiagfrob row: 4\nDiagfrob row: 5"}︡{"stdout":"\ncomputing G^(k) for k = 1..1\ncomputing C_i\n10%"}︡{"stdout":"\n20%\n30%"}︡{"stdout":"\n40%\n50%"}︡{"stdout":"\n60%\n70%"}︡{"stdout":"\n80%\n90%\ncomputing C_i^(-1)"}︡{"stdout":"\n7%\n15%\n23%\n30%\n38%\n46%\n53%\n61%\n69%\n76%\n84%\n92%\nComputing Ap\n"}︡{"stdout":"\nCPU time: 1.70 s, Wall time: 2.02 s"}︡{"stdout":"\n"}︡{"done":true}︡
︠909cfd10-d77f-4b03-af3c-718c624680f9s︠
family.ZetaFunction(3)
︡38e05177-e06a-40df-a79f-1431abfc5b6f︡{"stdout":"ChiiCapped = [3 + 6*7 + O(7^2), 3*7 + O(7^2), 6*7 + 5*7^2 + O(7^3), 3*7^2 + O(7^3), 3*7^2 + O(7^3), 7^3 + O(7^4)]\nNChii = [2, 2, 3, 3, 3, 4]\n[1, -4, 21, -56, 147, -196, 343]\n(343*T^6 - 196*T^5 + 147*T^4 - 56*T^3 + 21*T^2 - 4*T + 1)/(7*T^2 - 8*T + 1)\n"}︡{"done":true}︡
︠855cfefc-b196-494f-a7a7-d778f7a968ab︠









