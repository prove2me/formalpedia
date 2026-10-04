-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_ge_log_inv_of_lt_one_r16
-- name    : RybinAI2026.P01.psi_ge_log_inv_of_lt_one_r16
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-03T00:49:04.788603+00:00
-- url     : https://prove2.me/theorems/e5d0e85f-2a66-4527-84ac-29bc4292a898
-- title:
--   Small-argument psi integral is at least log of the reciprocal
-- statement:
--   For 0 < t < 1 the integrand 1/(1 + (t-1) s^2) dominates 1/(1 - (1-t) s^2), and on [0,1] the latter denominator is at least (1-s) + t. Its integral over [0,1] is exactly log((1+t)/t) = log(1+t) - log(t) >= log(1/t). Hence the small-argument psi integral grows like log(1/t), which is what makes the first directional integral large when the diagonal entry is tiny.
-- source:
--   namespace RybinAI2026.P01
--
--   theorem psi_ge_log_inv_of_lt_one_r16 (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
--       (Real.log (1 / t)) ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
--     classical
--     have hc : Continuous fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹ := by
--       fun_prop
--     have hnn : ∀ s : ℝ, 0 ≤ (1 + (t - 1) * s ^ 2)⁻¹ := by
--       intro s
--       have h : 0 < 1 + (t - 1) * s ^ 2 := by positivity
--       positivity
--     have hpt (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
--         (1 + (t - 1) * s ^ 2)⁻¹ ≥ 1 / ((1 - s) + t) := by
--       have hd : 0 < (1 - s) + t := by linarith
--       have he : 1 + (t - 1) * s ^ 2 ≤ (1 - s) + t := by
--         have h1 : (1 - s) * (1 + s) = 1 - s ^ 2 := by ring
--         have h2 : (0:ℝ) ≤ (1 - s) * t := by positivity
--         nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - s by linarith) (show (0:ℝ) ≤ t by linarith)]
--       rw [inv_le_inv₀ hd h]
--       exact he
--     have hbig : (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹)
--         ≥ ∫ _ s in (0 : ℝ)..1, (1 / ((1 - s) + t)) :=
--       setIntegral_le_integral_of_pointwise hnn (fun s hs => hpt s hs.1.le hs.2)
--     have heval : (∫ s in (0 : ℝ)..1, (1 / ((1 - s) + t))) = Real.log (1 + t) - Real.log t := by
--       have hsub : (fun s : ℝ => (1 / ((1 - s) + t))) = fun s : ℝ => (1 / (s + t)) := by
--         funext s
--         have : (1 - s) + t = (s + t) - 2 * s := by ring
--         rw [this]
--         by_cases hs : s = 0
--         · rw [hs]; ring
--         · have hne : s + t ≠ s + t - 2 * s := by linarith
--           field_simp
--       rw [show (∫ s in (0 : ℝ)..1, (1 / ((1 - s) + t))) = ∫ s in (0 : ℝ)..1, (1 / (s + t)) by
--         rw [hsub]]
--       have hfun : ContinuousOn fun s : ℝ => (1 / (s + t)) (Set.Icc (0:ℝ) 1) :=
--         ContinuousOn.inv₀ continuousOn_id continuousOn_const
--           (fun s hs => ne_of_gt (by linarith [hs.1] : 0 < s + t))
--       have hint : (1 / (s : ℝ) + t) = (Real.log ((1:ℝ) + t) - Real.log t) := by
--         have h1 : (0:ℝ) < 1 + t := by linarith
--         have h2 : (0:ℝ) < t := ht
--         rw [← Real.log_inv (by positivity : (0:ℝ) < 1 / (1 + t))]
--         rw [Real.one_div]
--         rw [Real.log_inv h2, Real.log_div]
--         norm_num
--         ring
--       have hconv := intervalIntegral.integral_eq_sub_of_hasDerivAt
--         (f := fun s : ℝ => Real.log (s + t)) (a := (0:ℝ)) (b := 1)
--         (fun s _ => Real.hasDerivAt_log (show (0:ℝ) < s + t by linarith [ht]))
--         (by norm_num)
--       rw [hconv]
--       norm_num
--       linarith
--     rw [hbig, heval]
--     have hlt : Real.log (1 + t) ≤ Real.log (1 / t) := by
--       rw [Real.le_log_iff]
--       simp only [one_div]
--       have : (1:ℝ) + t ≤ 1 / t := by
--         apply (div_le_iff₀ ht).2
--         nlinarith [sq_nonneg (1 - t)]
--       linarith
--     linarith
--   end RybinAI2026.P01

import Mathlib
set_option autoImplicit false
open MeasureTheory

namespace RybinAI2026.P01

/-- For `0 < t < 1` the kernel `1/(1 + (t-1) s^2)` is at least `1/(1 - (1-t) s^2)`, and for
`0 <= s <= 1` the denominator obeys `1 - (1-t) s^2 >= (1-s) + t`.  Therefore
`(∫ s in 0..1, (1 + (t-1) s^2)⁻¹) >= (Real.log (1 + t) - Real.log t) >= Real.log (1/t)`.
This is the elementary lower bound on the small-argument psi integral used to bound the first
directional integral from below in the geometric-affinity refutation. -/
theorem psi_ge_log_inv_of_lt_one_r16 (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (Real.log (1 / t)) ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by sorry

end RybinAI2026.P01
