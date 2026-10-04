-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_lower_inv_ge_one_r21
-- name    : RybinAI2026.P01.psi_lower_inv_ge_one_r21
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T07:45:46.109723+00:00
-- url     : https://prove2.me/theorems/cf8895d9-6859-4c53-b4a0-792841f06b48
-- title:
--   psi integral on [0,1] is at least 1/sqrt(t) when 1 <= t
-- statement:
--   When t >= 1 and s ranges over [0,1], the denominator 1 + (t-1)s^2 is at most t, so the reciprocal integrand is at least 1/t and integrating over the unit interval gives psi t >= 1/t.
-- source:
--   namespace RybinAI2026.P01
--
--   theorem psi_lower_inv_ge_one_r21 (t : ℝ) (ht1 : 1 ≤ t) :
--       (1 / t) ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
--     classical
--     have hle : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 1 + (t - 1) * s ^ 2 ≤ t := by
--       intro s hs0 hs1
--       have hs1' : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg (s + 1), sq_nonneg (s - 1)]
--       have htn : (0:ℝ) ≤ t - 1 := by linarith
--       have hmul : (0:ℝ) ≤ (t - 1) * s ^ 2 := mul_nonneg htn (sq_nonneg s)
--       linarith
--     have hlo : ∀ s : ℝ, (0:ℝ) ≤ 1 + (t - 1) * s ^ 2 := by
--       intro s
--       have htn : (0:ℝ) ≤ t - 1 := by linarith
--       linarith [mul_nonneg htn (sq_nonneg s)]
--     have hcont : Continuous fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹ := by
--       have h : Continuous fun s : ℝ => 1 + (t - 1) * s ^ 2 := by fun_prop
--       exact h.inv₀ fun s => ne_of_gt (hlo s)
--     have hint : IntervalIntegrable (fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹) volume 0 1 :=
--       hcont.intervalIntegrable _ _
--     have hpt : ∀ s ∈ Icc (0 : ℝ) 1, (1 / t) ≤ (1 + (t - 1) * s ^ 2)⁻¹ := by
--       intro s hs
--       rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s)] at hs
--       simp only [Icc.mem_eq, Set.mem_Icc] at hs
--       have ht : (0:ℝ) < t := by linarith
--       exact (inv_le_inv₀ (hlo s) ht).2 (hle s hs.1 hs.2)
--     have hmono := intervalIntegral.integral_mono_on hint hint (fun s hs => hpt s hs)
--     have hone : (∫ s in (0 : ℝ)..1, fun _ => 1 / t) = 1 / t := by
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

/-- For `1 <= t` and `0 <= s <= 1` the denominator `1 + (t-1) s^2` is at most `t`, so the
reciprocal integrand is at least `1/t` and the psi integral over the unit interval is at least
`1/t`.  Applied at `t = 1/b` together with the proved exact coordinate formula for the second
directional integral of `diag(1, b)`, this bounds that integral from below by `4 sqrt(b)`, which
is the mechanism that defeats the universal half-geometric-affinity bound. -/
theorem psi_lower_inv_ge_one_r21 (t : ℝ) (ht1 : 1 ≤ t) :
    (1 / t) ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by sorry

end RybinAI2026.P01
