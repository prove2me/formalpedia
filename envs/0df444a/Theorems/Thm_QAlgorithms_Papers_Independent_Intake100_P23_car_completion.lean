-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_car_completion
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.car_completion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:46:54.797576+00:00
-- url     : https://prove2.me/theorems/36ea87f6-67d4-4076-84d3-07ade4ff9855
-- title:
--   Unique extension of CAR to the Hilbert completion
-- statement:
--   Let $Y$ be a real inner-product space and $H$ a complex Hilbert space. Suppose $\phi:Y\to B(H)$ is a real-linear self-adjoint-valued CAR representation, with anticommutator $2\langle x,y\rangle1$. Writing $\widehat Y$ for the Hilbert completion, there is a unique operator-norm-continuous extension $\widehat\phi:\widehat Y\to B(H)$, and this extension is again real linear, self-adjoint valued, and satisfies
--   $$\widehat\phi(x)\widehat\phi(y)+\widehat\phi(y)\widehat\phi(x)=2\langle x,y\rangle\,1.$$
--   This permits passage from pre-Hilbert label spaces to Hilbert label spaces.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 14, Theorem 8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section CAR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- PDF p.14, Theorem 8(4): unique continuous CAR extension to the completion.
The input real inner-product space E is not assumed complete. -/
theorem car_completion (phi : E → H →L[ℂ] H) (hphi : IsCAR phi) :
    ∃! F : UniformSpace.Completion E → H →L[ℂ] H,
      Continuous F ∧ (∀ y : E, F (y : UniformSpace.Completion E) = phi y) ∧ IsCAR F := by sorry

end CAR

end QAlgorithms.Papers.Independent.Intake100.P23

end
