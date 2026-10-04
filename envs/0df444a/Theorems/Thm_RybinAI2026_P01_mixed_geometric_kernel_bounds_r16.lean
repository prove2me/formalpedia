-- Prove2me | Theorems.Thm_RybinAI2026_P01_mixed_geometric_kernel_bounds_r16
-- name    : RybinAI2026.P01.mixed_geometric_kernel_bounds_r16
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T00:48:50.746125+00:00
-- url     : https://prove2.me/theorems/ab379896-1d48-4e38-92da-3a60ffef5f1f
-- title:
--   Pointwise bounds for the mixed geometric-mean kernel
-- statement:
--   Let b be positive and t nonnegative. Since 1 + b t^4 >= 1 and sqrt(1 + t^4) >= 1, the kernel 2 t^2 / ((1 + b t^4) sqrt(1 + t^4)) is at most 2 t^2, which controls the integral over [0,1]. When t >= 1 one additionally has t^2 <= t^4 <= 1 + b t^4, so the same kernel is at most 2, which controls the integral over any window [1, T]. These two pointwise facts replace the auxiliary quartic-integral estimate in the disproof of the geometric-affinity bound.
-- source:
--   namespace RybinAI2026.P01
--
--   theorem mixed_geometric_kernel_bounds_r16 (b t : ℝ) (hb : 0 < b) :
--       ((Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4) ≤ 2 * t ^ 2) ∧
--       ((1 : ℝ) ≤ t -> (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4) ≤ 2) := by
--     classical
--     have hd : 0 < 1 + b * t ^ 4 := by positivity
--     have hs : 0 < Real.sqrt (1 + t ^ 4) := Real.sqrt_pos.2 (by positivity)
--     constructor
--     · have h1 : (1 : ℝ) ≤ 1 + b * t ^ 4 := by positivity
--       have h2 : (1 : ℝ) ≤ Real.sqrt (1 + t ^ 4) := by rw [Real.le_sqrt]; positivity
--       have hpos : 0 ≤ 2 * t ^ 2 := by positivity
--       nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ Real.sqrt (1+t^4)⁻¹ * 2 * t^2)]
--     · intro ht
--       have h4 : 1 ≤ t ^ 4 := by nlinarith [sq_nonneg (t - 1)]
--       have h1 : t ^ 2 ≤ 1 + b * t ^ 4 := by nlinarith
--       have h2 : (1 : ℝ) ≤ Real.sqrt (1 + t ^ 4) := by rw [Real.le_sqrt]; positivity
--       nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ Real.sqrt (1+t^4)⁻¹ * 2)]
--   end RybinAI2026.P01

import Mathlib
set_option autoImplicit false
open MeasureTheory

namespace RybinAI2026.P01

/-- The two pointwise bounds on the mixed geometric-mean kernel `f t = 2 t^2 / ((1 + b t^4) sqrt (1 + t^4))`
that drive the split estimate: on `[0,1]` one has `f t <= 2 t^2`, and for every `t >= 1` one has
`f t <= 2`.  Both follow from `1 + b t^4 >= 1`, `sqrt (1 + t^4) >= 1` and `t^2 <= t^4`. -/
theorem mixed_geometric_kernel_bounds_r16 (b t : ℝ) (hb : 0 < b) :
    ((Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4) ≤ 2 * t ^ 2) ∧
    ((1 : ℝ) ≤ t -> (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4) ≤ 2) := by sorry

end RybinAI2026.P01
