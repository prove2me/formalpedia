-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_matching_mobius_factorization
-- name    : QuantumBipartiteTesting.Bipartiteness.matching_mobius_factorization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:38:25.874773+00:00
-- url     : https://prove2.me/theorems/2d70d862-540c-4176-a41b-751e0ec0d008
-- title:
--   Möbius matching moments have the predicted homogeneous factor
-- statement:
--   Let $d_{i,j}$ be nonnegative integer counts on $k$ labeled components and finitely many colors, with total count $e=\sum_{i,j}d_{i,j}\le 2q$. For a partition $r$, put
--
--   $$
--   F_r(M,l)=\prod_{S\in r}\prod_j\prod_{a=0}^{\sum_{i\in S}d_{i,j}-1}\frac{l}{M-(2a+1)l}.
--   $$
--
--   Write $D_q(M,l)=\prod_{a=0}^{2q-1}(M-(2a+1)l)^{\lfloor2q/(a+1)\rfloor}$ and $D=\sum_{a=0}^{2q-1}\lfloor2q/(a+1)\rfloor$. For each partition $p$, there is a real bivariate polynomial $H_p$ of total degree at most $D$ such that, whenever $l\ne0$ and $D_q(M,l)\ne0$,
--
--   $$
--   \sum_{r\le p}\mu(r,p)F_r(M,l)=\frac{l^{e+k-|p|}H_p(M,l)}{D_q(M,l)}.
--   $$
--
--   Here $\mu$ is the partition Möbius coefficient defined by signed refinement chains. This count-matrix identity supplies the cancellation needed to extract the cycle-rank power in graph topology moments, and also applies to other finite color sets.
-- source:
--   Ambainis–Childs–Liu, Quantum Property Testing for Bounded-Degree Graphs, https://arxiv.org/pdf/1012.3174, Proposition 6, printed pp.8–9 and Appendix C.5, pp.19–21. Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Appendix A.2, equations (A.5)–(A.7), pp.30–31. This states the component-count form with an arbitrary finite color set.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness Finset
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.matching_mobius_factorization {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (q : ℕ)
    (he : (∑ i, ∑ j, d i j) ≤ 2*q) (p : Partition k) :
    ∃ H : Bivariate, H.totalDegree ≤ DenominatorDegree q ∧
      ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
        (∑ r : Partition k, if Refines r p then (Mobius r p:ℝ) *
          (∏ S ∈ Blocks r, ∏ j : Fin colors, MatchingMoment (∑ i ∈ S, d i j) M l) else 0) =
        l^((∑ i, ∑ j, d i j)+k-(Blocks p).card) * Eval H M l / Eval (Denominator q) M l := by sorry
