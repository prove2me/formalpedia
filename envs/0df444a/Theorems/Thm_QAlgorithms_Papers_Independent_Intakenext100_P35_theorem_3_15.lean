-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_3_15
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_3_15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:17:14.834579+00:00
-- url     : https://prove2.me/theorems/13567c20-7643-43ab-b763-6468fcc73145
-- title:
--   Theorem 3.15
-- statement:
--   Let $A$ satisfy GSF, and let $(f_k)$ and its pointwise limit $f$ satisfy all the boundedness and local derivative assumptions of Lemma 3.5. Then
--
--   $$f_k(A)x\longrightarrow f(A)x\qquad(x\in X).$$
--
--   Thus the B-calculus converges in the strong operator topology. No additional symbol $g$ or operator hypothesis is imposed.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 14, Theorem 3.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 3.15, arXiv:2202.03143v1, PDF page(s) 14. -/
theorem theorem_3_15
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hA : GSF A) (fs : ℕ → AnalyticSymbol) (f : AnalyticSymbol)
(hfs : BConvergence fs f) :
    BesovClass f ∧ ∀ x : X, Tendsto (fun n => bOperator A (fs n) x)
      atTop (𝓝 (bOperator A f x)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
