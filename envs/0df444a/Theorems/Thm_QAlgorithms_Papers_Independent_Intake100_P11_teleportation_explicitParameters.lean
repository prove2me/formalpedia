-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_teleportation_explicitParameters
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.teleportation_explicitParameters
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:54:45.34209+00:00
-- url     : https://prove2.me/theorems/3b2c9b87-901a-453f-b5c9-f3394438d4bf
-- title:
--   Explicit measurement settings on the nonsingular cotangent chart
-- statement:
--   Let $S=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ with $ad-bc=1$. Choose real $\theta_0,\theta_1$ such that both sines are nonzero and $\cos(\theta_0-\theta_1)>0$. Define $t=\cot\theta_0$, $D=2c-(1+d)t$, and $E=c-dt$. Assume $D\ne0$, $E\ne0$, and $\cot\theta_1=(1-d)/D$. Set
--
--   $$
--   k_3=c-(1+d)t,\qquad k_4=\frac{1-a+bt}{E}.
--   $$
--
--   For the elementary matrix $M(k)=\begin{pmatrix}-k&-1\\1&0\end{pmatrix}$ and the corrected teleportation matrix $T$,
--
--   $$
--   M(k_4)M(k_3)T(\theta_0+\theta_1,\theta_0-\theta_1)=S.
--   $$
--
--   This is an explicit chart for programming the fixed-coupling construction. The unrestricted existence result is the separate universality theorem; this rational chart does not cover every target.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 7, §V, Eq.(14), continued p.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF pp.7--8, Eq.(14): cotangent chart on its actual domain.
Printed p.8 asserts zero denominators can be avoided by theta0. Changed: guard
all chart denominators and sines; c=0,d=-1 makes D identically zero, so this
chart is not all-target. Full universality is separately stated. This source
qualification requires independent moderation. -/
theorem teleportation_explicitParameters
    (A : Mat2) (hA : IsOneModeSymplectic A) (theta0 theta1 : ℝ)
    (hSin0 : Real.sin theta0 ≠ 0) (hSin1 : Real.sin theta1 ≠ 0)
    (hCos : 0 < Real.cos (theta0 - theta1))
    (hD : 2 * A 1 0 - (1 + A 1 1) * cotAngle theta0 ≠ 0)
    (hE : A 1 0 - A 1 1 * cotAngle theta0 ≠ 0)
    (hCot : cotAngle theta1 =
      (1 - A 1 1) / (2 * A 1 0 - (1 + A 1 1) * cotAngle theta0)) :
    let kappa3 := A 1 0 - (1 + A 1 1) * cotAngle theta0
    let kappa4 := (1 - A 0 0 + A 0 1 * cotAngle theta0) /
      (A 1 0 - A 1 1 * cotAngle theta0)
    elementary kappa4 * elementary kappa3 *
      teleportationMatrix (theta0 + theta1) (theta0 - theta1) = A := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
