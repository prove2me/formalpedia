-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_le_inv_of_le_one_r21
-- name    : RybinAI2026.P01.psi_le_inv_of_le_one_r21
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T07:45:41.608299+00:00
-- url     : https://prove2.me/theorems/24bbd471-6bb2-4849-bd38-93b0b49c1bd9
-- title:
--   psi integral on [0,1] is at most 1/t when t <= 1
-- statement:
--   When 0 < t <= 1 and s ranges over [0,1], the denominator 1 + (t-1) s^2 equals t plus the nonneg quantity (1-t)(1-s^2), so it is at least t. Taking reciprocals and integrating over [0,1] of length 1 gives psi t <= 1/t.
-- source:
--   namespace RybinAI2026.P01
--
--   theorem psi_le_inv_of_le_one_r21 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
--       (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) ≤ 1 / t := by
--     classical
--     have harg : ∀ s : ℝ, 0 ≤ 1 + (t - 1) * s ^ 2 := by
--       intro s
--       have h1 : (0:ℝ) ≤ 1 := by norm_num
--       have h2 : (0:ℝ) ≤ s ^ 2 := sq_nonneg s
--       have h3 : (0:ℝ) ≤ 1 - t := by linarith
--       linarith [mul_nonneg h3 h2]
--     have hcont : Continuous fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹ := by
--       have h : Continuous fun s : ℝ => 1 + (t - 1) * s ^ 2 := by fun_prop
--       exact h.inv₀ fun s => ne_of_gt (harg s)
--     have hint : IntervalIntegrable (fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹) volume 0 1 :=
--       hcont.intervalIntegrable _ _
--     have hsq : ∀ s : ℝ, 0 ≤ s ^ 2 := fun s => sq_nonneg s
--     have hbound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → t ≤ 1 + (t - 1) * s ^ 2 := by
--       intro s hs0 hs1
--       have hs1' : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg (s + 1), sq_nonneg (s - 1)]
--       have hnon : (0:ℝ) ≤ (1 - t) * (1 - s ^ 2) := by
--         have h1 : (1:ℝ) ≤ 1 := by norm_num
--         have h3 : (0:ℝ) ≤ 1 - t := by linarith
--         linarith [mul_nonneg h3 (by linarith)]
--       have hid : 1 + (t - 1) * s ^ 2 = t + (1 - t) * (1 - s ^ 2) := by ring
--       linarith
--     have hpt : ∀ s ∈ Icc (0 : ℝ) 1, (1 + (t - 1) * s ^ 2)⁻¹ ≤ t⁻¹ := by
--       intro s hs
--       rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s)] at hs
--       simp only [Icc.mem_eq, Set.mem_Icc] at hs
--       exact div_le_div_of_nonneg_right (hbound s hs.1 hs.2) (by positivity)
--     have hmono := intervalIntegral.integral_mono_on hint hint (fun s hs => hpt s hs)
--     have hone : (∫ s in (0 : ℝ)..1, fun _ => t⁻¹) = t⁻¹ := by
--       rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
--         intervalIntegral.integral_one, one_mul]
--     rw [hone] at hmono
--     exact hmono
--
--   end RybinAI2026.P01

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

namespace RybinAI2026.P01

/-- For `0 < t <= 1` and `0 <= s <= 1` the denominator `1 + (t-1) s^2` is `t` plus the
nonnegative quantity `(1-t)(1-s^2)`, so it is at least `t`.  Taking reciprocals and integrating
over the unit interval gives the upper bound below, which keeps the first directional integral of
`diag(1, b)` bounded above in the geometric-affinity refutation. -/
theorem psi_le_inv_of_le_one_r21 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) ≤ 1 / t := by sorry

end RybinAI2026.P01
