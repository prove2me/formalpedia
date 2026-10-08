-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_cpow_negative_real_boundary
-- name    : WeightedRootIntegralIdentity.cpow_negative_real_boundary
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T14:41:29.648007+00:00
-- url     : https://prove2.me/theorems/e7bea59d-dca5-40d2-87f3-d68c33f1c6d2
-- title:
--   Boundary values of a complex power on the negative axis
-- statement:
--   Let $r\ge0$ and $w\in\mathbb R$. For the principal branch of the complex power, the upper boundary value on the negative real axis and its conjugate are
--
--   $$
--   (-r)^w=r^w e^{i\pi w},\qquad \overline{(-r)^w}=r^w e^{-i\pi w}.
--   $$
--
--   This factorwise phase formula is the local boundary-value input for computing the jump of a weighted product of powers across a branch cut.
-- source:
--   Boundary-value formula used in the contour proof at https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals, especially the phase relation preceding the jump calculation in the first answer.

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace WeightedRootIntegralIdentity

theorem cpow_negative_real_boundary
    (r w : ℝ) (hr : 0 ≤ r) :
    ((-(r : ℂ)) ^ (w : ℂ) =
        (Real.rpow r w : ℂ) * Complex.exp (((Real.pi * w : ℝ) : ℂ) * Complex.I)) ∧
    (starRingEnd ℂ ((-(r : ℂ)) ^ (w : ℂ)) =
        (Real.rpow r w : ℂ) * Complex.exp (-(((Real.pi * w : ℝ) : ℂ) * Complex.I))) := by sorry

end WeightedRootIntegralIdentity
