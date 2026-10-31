-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_car_fieldExponential
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.car_fieldExponential
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:45:01.012466+00:00
-- url     : https://prove2.me/theorems/c3edf623-889c-4327-8dd0-c2e7202ecb34
-- title:
--   Exponential of a bounded CAR field
-- statement:
--   Let $Y$ be a real inner-product space, not necessarily complete, and $H$ a complex Hilbert space. Let $\phi:Y\to B(H)$ be real linear, self-adjoint valued, and satisfy $\phi(x)\phi(y)+\phi(y)\phi(x)=2\langle x,y\rangle\,1$. Then for every $y\in Y$,
--   $$e^{i\phi(y)}=\cos\|y\|\,1+i\frac{\sin\|y\|}{\|y\|}\phi(y).$$
--   At $y=0$ the identity is read as $1=1$ since $\phi(0)=0$. This computes the entire bounded exponential from the CAR square identity. **Formalization Note** Lean's quotient at zero is multiplied by the zero operator, so the same expression represents this case faithfully.
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

/-- PDF p.14, Theorem 8(3): the bounded field exponential.
At zero, the quotient is multiplied by phi(0)=0, so the formula gives 1. -/
theorem car_fieldExponential (phi : E → H →L[ℂ] H) (hphi : IsCAR phi) (y : E) :
    NormedSpace.exp (Complex.I • phi y) =
      (Real.cos ‖y‖ : ℂ) • (1 : H →L[ℂ] H) +
        (Complex.I * ((Real.sin ‖y‖ / ‖y‖ : ℝ) : ℂ)) • phi y := by sorry

end CAR

end QAlgorithms.Papers.Independent.Intake100.P23

end
