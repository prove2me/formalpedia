-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_canonical_concatenation
-- name    : QAlgorithms.Papers.Independent.Support21.P16.canonical_concatenation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:43:18.732506+00:00
-- url     : https://prove2.me/theorems/d349650d-0b2e-40af-8bcb-4eea9758b634
-- title:
--   Canonical cloners concatenate exactly
-- statement:
--   Let $d>0$ and $1\le N<M<R$ be integers. Write $D_k=\binom{d+k-1}{k}$, let $s_k$ be the Bose projector, and define $\widehat T_{ba}(A)=(D_a/D_b)s_b((s_aAs_a)\otimes I^{\otimes(b-a)})s_b$. Then, as zero-extended maps,
--   $$
--   \widehat T_{RM}\circ\widehat T_{MN}=\widehat T_{RN}.
--   $$
--   For $c_k=k/(d+k)$, the explicit coefficient $g_{MN}=N(d+M)/(M(d+N))$ equals $c_N/c_M$ and is a valid Black Cow coefficient of $\widehat T_{MN}$: for every Bose-supported $A$,
--   $$
--   R_M(\widehat T_{MN}(A))=\frac{c_N}{c_M}R_N(A)
--   +\left(1-\frac{c_N}{c_M}\right)\operatorname{tr}(A)\frac{I}{d},
--   $$
--   where $R_k$ is the first-site restriction.
--
--   This preserves the source's map identity and pins its coefficient factorization to the explicit formula, including a valid representative at $d=1$.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 7, canonical-concatenation

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.7: the actual canonical maps concatenate, and their coefficient
has the explicit quotient form fixed by Eq.(3.8), not an arbitrary family. -/
theorem canonical_concatenation (d N M R : ℕ) (hd : 0 < d) (hN : 1 ≤ N)
    (hNM : N < M) (hMR : M < R) :
    (canonicalCloner (d := d) hMR.le ∘ canonicalCloner hNM.le) =
      canonicalCloner (Nat.le_trans hNM.le hMR.le) ∧
    canonicalCoefficient d N M = coefficientFactor d N / coefficientFactor d M ∧
    HasBlackCowCoefficient hN (by omega) (canonicalCloner (d := d) hNM.le)
      (coefficientFactor d N / coefficientFactor d M) := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
