-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_corollary_3_20
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.corollary_3_20
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:19:14.624759+00:00
-- url     : https://prove2.me/theorems/9dada379-707c-4fdc-9dc0-0d8c8a1b3395
-- title:
--   Corollary 3.20
-- statement:
--   Let $-A$ generate a bounded C0-semigroup on a Hilbert space and suppose $A$ has a bounded inverse. There exist $C>0$ and $T>1$, depending on $A$, such that
--
--   $$\|e^{-tA^{-1}}\|\le C\log t\qquad(t\ge T).$$
--
--   The exponential is the norm-defined exponential of the bounded operator $-tA^{-1}$. The conclusion is an upper bound, with no assertion of sharpness.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 17, Corollary 3.20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Corollary 3.20, arXiv:2202.03143v1, PDF page(s) 17. -/
theorem corollary_3_20
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hA : HilbertGenerator A)
(R : X →L[ℂ] X) (hR : InverseAt A 0 R) :
    ∃ C T : ℝ, 0 < C ∧ 1 < T ∧ ∀ t : ℝ, T ≤ t →
      ‖NormedSpace.exp ((-(t : ℂ)) • R)‖ ≤ C * Real.log t := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
