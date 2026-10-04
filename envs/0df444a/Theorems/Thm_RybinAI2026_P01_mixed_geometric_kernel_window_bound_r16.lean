-- Prove2me | Theorems.Thm_RybinAI2026_P01_mixed_geometric_kernel_window_bound_r16
-- name    : RybinAI2026.P01.mixed_geometric_kernel_window_bound_r16
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T00:49:19.750216+00:00
-- url     : https://prove2.me/theorems/7d4216c6-6e15-46b0-984b-2631500d0f33
-- title:
--   Window split estimate for the mixed geometric-mean kernel
-- statement:
--   Fix positive b and a window endpoint T >= 1. Split the integral at 1. On [0,1] the kernel is at most 2 t^2, whose integral is 2/3. On [1,T] the kernel is at most 2, whose integral is 2(T-1). Adding the two gives 2/3 + 2(T-1) = 2T - 4/3. Applied with T = 2^16 this bounds the mixed geometric-mean integral appearing in the geometric-affinity refutation.
-- source:
--   namespace RybinAI2026.P01
--
--   theorem mixed_geometric_kernel_window_bound_r16 (b T : ℝ) (hb : 0 < b) (hT1 : 1 ≤ T) :
--       (∫ t in (0 : ℝ)..T, (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4)) ≤
--         2 / 3 + 2 * (T - 1) := by
--     classical
--     let f : ℝ → ℝ := fun t => (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4)
--     have hf : Continuous f := by
--       have hd : Continuous fun t : ℝ => 1 + b * t ^ 4 := by fun_prop
--       have hs : Continuous fun t : ℝ => Real.sqrt (1 + t ^ 4) := by
--         fun_prop
--       fun_prop
--     have hnn : ∀ t : ℝ, 0 ≤ f t := by
--       intro t
--       have hd : 0 < 1 + b * t ^ 4 := by positivity
--       have hs : 0 < Real.sqrt (1 + t ^ 4) := Real.sqrt_pos.2 (by positivity)
--       positivity
--     have hbnd := mixed_geometric_kernel_bounds b T hb
--     have hA : (∫ t in (0 : ℝ)..1, f t) ≤ 2 / 3 := by
--       calc
--         (∫ t in (0 : ℝ)..1, f t) ≤ ∫ _ t in (0 : ℝ)..1, (2 : ℝ) * t ^ 2 :=
--           setIntegral_le_integral_of_pointwise (fun _ _ => hnn _)
--             (fun t ht => by simpa [f] using (hbnd.1 t))
--         _ = 2 / 3 := by norm_num
--     have hB : (∫ t in (1 : ℝ)..T, f t) ≤ 2 * (T - 1) := by
--       calc
--         (∫ t in (1 : ℝ)..T, f t) ≤ ∫ _ t in (1 : ℝ)..T, (2 : ℝ) :=
--           setIntegral_le_integral_of_pointwise (fun _ _ => hnn _)
--             (fun t ht => by simpa [f] using (hbnd.2 t ht.1.le))
--         _ = 2 * (T - 1) := by norm_num
--     rw [intervalIntegral.integral_add_adjacent_intervals hf (by norm_num) hT1]
--     linarith
--   end RybinAI2026.P01

import Mathlib
set_option autoImplicit false
open MeasureTheory

namespace RybinAI2026.P01

/-- Split estimate for the mixed geometric-mean kernel.  For positive `b` and any `T >= 1` the
integral of `2 t^2 / ((1 + b t^4) sqrt (1 + t^4))` over `[0, T]` is at most `2/3 + 2 (T - 1)`,
using `mixed_geometric_kernel_bounds` on `[0,1]` and `[1,T]`.  This is the only integral
estimate the disproof of `one_sphere_geometric_affinity` needs. -/
theorem mixed_geometric_kernel_window_bound_r16 (b T : ℝ) (hb : 0 < b) (hT1 : 1 ≤ T) :
    (∫ t in (0 : ℝ)..T, (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4)) ≤
      2 / 3 + 2 * (T - 1) := by sorry

end RybinAI2026.P01
