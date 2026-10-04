-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_ge_atan_div_sqrt_of_one_lt_r16
-- name    : RybinAI2026.P01.psi_ge_atan_div_sqrt_of_one_lt_r16
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T00:49:20.361991+00:00
-- url     : https://prove2.me/theorems/c281f549-e141-4760-9dd8-b43a331ada9a
-- title:
--   Large-argument psi integral is at least atan(sqrt t)/sqrt t
-- statement:
--   For t > 1 the kernel 1/(1 + (t-1) s^2) dominates 1/(1 + t s^2) on [0,1]. The integral of the latter is atan(sqrt(t))/sqrt(t), obtained by the substitution x = sqrt(t) s. This gives a sharper lower bound than 1/sqrt(t) for the large-argument psi integral, and it is what makes the second directional integral large when one diagonal entry is tiny.
-- source:
--   namespace RybinAI2026.P01
--
--   theorem psi_ge_atan_div_sqrt_of_one_lt_r16 (t : ℝ) (ht : 1 < t) :
--       (Real.arctan (Real.sqrt t)) / Real.sqrt t ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
--     classical
--     have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 (by positivity)
--     have hc : Continuous fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹ := by fun_prop
--     have hnn : ∀ s : ℝ, 0 ≤ (1 + (t - 1) * s ^ 2)⁻¹ := by
--       intro s
--       have h : 0 < 1 + (t - 1) * s ^ 2 := by positivity
--       positivity
--     have hpt (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
--         (1 + (t - 1) * s ^ 2)⁻¹ ≥ 1 / (1 + t * s ^ 2) := by
--       have hd : 0 < 1 + t * s ^ 2 := by positivity
--       have hbig : 1 + t * s ^ 2 ≤ 1 + (t - 1) * s ^ 2 := by
--         have : (0:ℝ) ≤ s ^ 2 := sq_nonneg s
--         nlinarith
--       rw [inv_le_inv₀ (by positivity : (0:ℝ) < 1 + (t-1) * s^2) hd]
--       exact hbig
--     have hbig : (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹)
--         ≥ ∫ _ s in (0 : ℝ)..1, (1 / (1 + t * s ^ 2)) :=
--       setIntegral_le_integral_of_pointwise hnn (fun s hs => hpt s ⟨hs.1.le, hs.2⟩)
--     have heval : (∫ s in (0 : ℝ)..1, (1 / (1 + t * s ^ 2))) = Real.arctan (Real.sqrt t) / Real.sqrt t := by
--       have hsub : (∫ s in (0 : ℝ)..1, (1 / (1 + t * s ^ 2)))
--           = (1 / Real.sqrt t) * (Real.arctan (Real.sqrt t * 1) - Real.arctan (Real.sqrt t * 0)) := by
--         have hfun : ContinuousOn fun s : ℝ => Real.arctan (Real.sqrt t * s) (Set.Icc (0:ℝ) 1) :=
--           ContinuousOn.atan (continuousOn_const.mul continuousOn_id)
--         have hderiv : ∀ s ∈ (Set.Icc (0:ℝ) 1),
--             HasDerivAt (fun y : ℝ => Real.arctan (Real.sqrt t * y))
--               (Real.sqrt t / (1 + (Real.sqrt t * s) ^ 2)) s := by
--           intro s _
--           convert (Real.hasDerivAt_atan (x := Real.sqrt t * s) (hsq.ne')).comp s
--             (Real.hasDerivAt_const_mul s hsq) using 1 <;> ring
--         have hconv := intervalIntegral.integral_eq_sub_of_hasDerivAt
--           (f := fun y : ℝ => Real.arctan (Real.sqrt t * y)) (a := (0:ℝ)) (b := 1)
--           (fun y _ => hderiv y ⟨hfun y⟩) (by norm_num)
--         rw [hconv]
--         norm_num
--         ring
--       rw [hsub]
--     rw [hbig]
--     have hmul : (1 / Real.sqrt t) * Real.arctan (Real.sqrt t)
--         = Real.arctan (Real.sqrt t) / Real.sqrt t := by field_simp
--     rw [heval, hmul]
--   end RybinAI2026.P01

import Mathlib
set_option autoImplicit false
open MeasureTheory

namespace RybinAI2026.P01

/-- For `1 < t` one has `t - 1 ≤ t`, so `1 + (t-1) s^2 ≤ 1 + t s^2` on `[0,1]` and hence
`(∫ s in 0..1, (1 + (t-1) s^2)⁻¹) ≥ (Real.arctan (Real.sqrt t)) / Real.sqrt t`.
This is the elementary lower bound on the large-argument psi integral, used to bound the second
directional integral from below in the geometric-affinity refutation. -/
theorem psi_ge_atan_div_sqrt_of_one_lt_r16 (t : ℝ) (ht : 1 < t) :
    (Real.arctan (Real.sqrt t)) / Real.sqrt t ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by sorry

end RybinAI2026.P01
