-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_nearest_centers_and_costs
-- name    : TightCoreset2027.Euclidean.nearest_centers_and_costs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:07:32.381974+00:00
-- url     : https://prove2.me/theorems/d948f246-0a7f-46b3-8496-0637913ee18c
-- title:
--   Claim 2.2 — nearest centers and costs
-- statement:
--   Take the §2.1 projection family, positive integer parameters $n,m,q,L$, the coding condition $2^L>q+\binom q3$, and $n(n-1)+m(L+1)\le k$. Let $X$ be the $n$-copy dataset defined above. For every active copy $b$, direction $v\in V$ and sign array $\sigma$, the prescribed padded query $C$ has exactly $k$ distinct centers and $|X|=n^2mq$. Every active point $p_{b,j,i,s}$ at level $\ell=\ell(s;v)$ has the translated $c_{i,\ell}$ as its unique nearest center, and
--
--   $$d(p_{b,j,i,s},C)^2=D_\ell+\frac{\sqrt n}{8L^2}\sigma_{ji}(-1)^\ell,\qquad 5n\le d(p_{b,j,i,s},C)^2\le9n.$$
--
--   Every inactive point has squared cost $2$, and
--
--   $$\operatorname{cost}_2(X,C)\le11|X|.$$
--
--   The assertion verifies all assignment and cost clauses for the concrete centers, including every populated cell, without assuming their correctness in the setup.
--
--   Differences from the source:
--   - encoding: sufficiently separated copies and sufficiently remote fixed padding → translations 20 sqrt(n) b f and padding 20 sqrt(n)(n+1+r) f; reason: the proof allows separation at least 20 sqrt(n); the fixed padding exceeds all copies and local query distances
--   - encoding: orthogonal coordinate blocks and signs in {-1,1} → a Euclidean space indexed by the disjoint coordinate blocks and Boolean sign arrays; reason: the coordinate change is isometric and each sign array is represented
--   - encoding: for every point in a populated cell, together with the constructed set sizes in the setup → indexed points with the specified level, and the set cardinalities included in the conclusion; reason: distinct triples parameterize the same cells; the size assertions are the explicit construction obligations from the preceding paragraphs
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Claim 2.2, Eq. (7)–(9), printed pp. 12–13 / PDF pp. 14–15; setup §§2.1–2.2, printed pp. 10–11 / PDF pp. 12–13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_queryConstruction
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

theorem nearest_centers_and_costs (n m L q k : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hcode : q + Nat.choose q 3 < 2 ^ L)
    (G : ProjectionFamily L q) (hG : ProjectionSpecification G)
    (hbudget : n * (n - 1) + m * (L + 1) ≤ k) :
    ∀ (b : Fin n) (v : ProjectionSpace L), v ∈ G.directions →
      ∀ σ : SignArray n m,
        let C := queryCenters n n m L k b (displacement2 L) v σ
        let X := dataset n n m G
        C.card = k ∧ X.card = n * n * m * q ∧
        (∀ (j : Fin n) (i : Fin m) (ℓ : Fin (L + 1)) (s : Fin q),
          G.level s v = ℓ →
            IsUniqueNearest (dataPoint G b.val j i s) C
              (activeCenter b.val (displacement2 L) v σ i ℓ) ∧
            nearestDistance (dataPoint G b.val j i s) C ^ 2 =
              baseline n L ℓ + Real.sqrt (n : ℝ) / (8 * (L : ℝ) ^ 2) *
                signValue (σ j i) * (-1 : ℝ) ^ ℓ.val ∧
            5 * (n : ℝ) ≤ nearestDistance (dataPoint G b.val j i s) C ^ 2 ∧
            nearestDistance (dataPoint G b.val j i s) C ^ 2 ≤ 9 * (n : ℝ)) ∧
        (∀ b' : Fin n, b' ≠ b → ∀ (j : Fin n) (i : Fin m) (s : Fin q),
          nearestDistance (dataPoint G b'.val j i s) C ^ 2 = 2) ∧
        cost 2 X C ≤ 11 * (X.card : ℝ) := by sorry

end TightCoreset2027.Euclidean
