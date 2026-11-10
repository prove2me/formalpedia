-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_paired_queries_detect_omissions
-- name    : TightCoreset2027.Euclidean.paired_queries_detect_omissions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:07:41.697735+00:00
-- url     : https://prove2.me/theorems/d15abee5-351f-47cc-80b6-70651e8dc3ed
-- title:
--   Proposition 2.3 — detecting omissions with paired queries
-- statement:
--   Use the concrete $n$-copy dataset $X$, projection family and query construction of §§2.1–2.2, with all positive integer parameters, $2^L>q+\binom q3$, and $n(n-1)+m(L+1)\le k$. Let $S\subseteq X$ have arbitrary nonnegative weights and satisfy $|S|\le|X|/2$. An active copy with at most half its points retained exists. For every such choice of active copy, there are $v\in V$ and $\sigma\in\{-1,1\}^{n\times m}$ whose prescribed query $C$ has exactly $k$ centers, positive true cost, and
--
--   $$\frac{|\operatorname{cost}_2(S,w,C)-\operatorname{cost}_2(X,C)|}{\operatorname{cost}_2(X,C)}\ge\frac1{176\sqrt3\sqrt{nq}\,L^2}.$$
--
--   The bound applies to all reweightings and needs no half-omission condition on individual groups. It is the numbered error estimate feeding the squared-distance lower bound.
--
--   Differences from the source:
--   - encoding: the associated family of sufficiently separated and padded queries → the explicit centers and common padding defined in queryConstruction; reason: these instantiate the source choices uniformly before weights and queries
--   - encoding: nonnegative weights on S and half-cardinality inequalities → ambient NNReal weights ignored outside S and doubled integer inequalities; reason: zero extension covers every source weighting, and doubling avoids natural division truncation
--   - encoding: choose an active copy as in Section 2.2 and divide by the true cost → existence of an active copy, the bound for every eligible copy, exactly k centers, and positive true cost; reason: the source averaging and cost lower bounds justify these setup facts and make the ratio unambiguous
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Proposition 2.3, Eq. (10), printed p. 14 / PDF p. 16; §2.2 active-copy choice, printed p. 11 / PDF p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_queryConstruction
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

theorem paired_queries_detect_omissions (n m L q k : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hcode : q + Nat.choose q 3 < 2 ^ L)
    (G : ProjectionFamily L q) (hG : ProjectionSpecification G)
    (hbudget : n * (n - 1) + m * (L + 1) ≤ k)
    (S : Finset (ConstructionSpace n m L))
    (w : ConstructionSpace n m L → NNReal)
    (hsubset : S ⊆ dataset n n m G)
    (hhalf : 2 * S.card ≤ (dataset n n m G).card) :
    (∃ b : Fin n, 2 * (S ∩ dataCopy n m G b.val).card ≤ (dataCopy n m G b.val).card) ∧
    ∀ b : Fin n,
      2 * (S ∩ dataCopy n m G b.val).card ≤ (dataCopy n m G b.val).card →
        ∃ v ∈ G.directions, ∃ σ : SignArray n m,
          let C := queryCenters n n m L k b (displacement2 L) v σ
          let X := dataset n n m G
          C.card = k ∧ 0 < cost 2 X C ∧
            1 / (176 * Real.sqrt 3 * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2) ≤
              |weightedCost 2 S w C - cost 2 X C| / cost 2 X C := by sorry

end TightCoreset2027.Euclidean
