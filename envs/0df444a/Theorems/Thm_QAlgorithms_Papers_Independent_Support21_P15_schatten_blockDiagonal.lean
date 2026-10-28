-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P15_schatten_blockDiagonal
-- name    : QAlgorithms.Papers.Independent.Support21.P15.schatten_blockDiagonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:34:27.815773+00:00
-- url     : https://prove2.me/theorems/46a414f7-55a7-4bd7-b5bc-7b03ac51f080
-- title:
--   Block-diagonal Schatten embedding and contractive pinching
-- statement:
--   Let $0<p<\infty$ and let $n,m\ge1$ be integers. Write $S_p^m$ for the complex $m\times m$ matrices with Schatten quasi-norm $\|A\|_p=(\operatorname{Tr}((A^*A)^{p/2}))^{1/p}$. The complex-linear map $B(A_1,\ldots,A_n)=\operatorname{diag}(A_1,\ldots,A_n)$ is injective and satisfies
--
--   $$
--   \|B(A_1,\ldots,A_n)\|_p=\left(\sum_{i=1}^n\|A_i\|_p^p\right)^{1/p}.
--   $$
--
--   For $p\ge1$, deleting the off-diagonal blocks defines a complex-linear projection $P$ onto the range of this same inclusion, with $\|P(A)\|_p\le\|A\|_p$ for every matrix $A$. Thus this range is 1-complemented in $S_p^{nm}$.
--
--   This identifies finite p-sums of Schatten blocks with concrete block-diagonal matrix subspaces. **Formalization Note** The target matrix rows and columns are indexed by $\mathrm{Fin}(n)\times\mathrm{Fin}(m)$; the Schatten formula is reused from the pinned accepted library.
-- source:
--   On subspaces of non-commutative L_p-spaces, arXiv:math/0307169v1, PDF p. 14, Unnumbered block-diagonal Schatten embedding

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P15

noncomputable section

open scoped BigOperators

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P15

/-- Unnumbered block-diagonal observation, arXiv:math/0307169v1, PDF p.14:
ell_p^n(S_p^m) embeds isometrically into S_p^(nm), with a contractive projection
onto that same range when p≥1. The Schatten size is the accepted all-matrix
trace-of-power formula, not the ambient entrywise matrix norm. -/
theorem schatten_blockDiagonal (p : ℝ) (hp : 0 < p)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Function.Injective (schattenBlockInclusion n m) ∧
    (∀ x : Fin n → Matrix (Fin m) (Fin m) ℂ,
      QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)
        (schattenBlockInclusion n m x) =
      finiteLpSize p
        (QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)) x) ∧
    (1 ≤ p →
      (schattenBlockProjection n m).comp (schattenBlockProjection n m) =
        schattenBlockProjection n m ∧
      LinearMap.range (schattenBlockProjection n m) =
        LinearMap.range (schattenBlockInclusion n m) ∧
      ∀ x : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ,
        QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p)
          (schattenBlockProjection n m x) ≤
        QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p) x) := by sorry

end QAlgorithms.Papers.Independent.Support21.P15

end
