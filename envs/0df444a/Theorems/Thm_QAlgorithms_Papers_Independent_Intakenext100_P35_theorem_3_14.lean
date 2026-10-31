-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_3_14
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_3_14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:16:53.37046+00:00
-- url     : https://prove2.me/theorems/f51b3f3f-1082-483f-911e-476051105a83
-- title:
--   Theorem 3.14
-- statement:
--   Let $A$ be closed and densely defined on a complex Banach space, with spectrum in the closed right half-plane. If $A$ admits a bounded B-calculus $\Phi$, then $A$ satisfies GSF and
--
--   $$\Phi(f)=\Phi_A(f)\qquad(f\in\mathcal B),$$
--
--   where $\Phi_A$ is determined by the concrete formula (3.15). This characterizes both existence and uniqueness of the calculus.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 14, Theorem 3.14

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 3.14, arXiv:2202.03143v1, PDF page(s) 14. -/
theorem theorem_3_14
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hsp : operatorSpectrum A ⊆ closedHp)
(F : AnalyticSymbol → X →L[ℂ] X) (hF : BCalculus A F) :
    GSF A ∧ ∀ f, BesovClass f → RealizesB A f (bOperator A f) ∧ F f = bOperator A f := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
