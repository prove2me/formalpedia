-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_frequency_alias_bound
-- name    : TaoFivePrimes.rh_high_height_gamma_frequency_alias_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T22:11:26.870894+00:00
-- url     : https://prove2.me/theorems/ba1dbbff-da2f-4bc9-b615-bbadfb0467b7
-- title:
--   TaoFivePrimes.rh_high_height_gamma_frequency_alias_bound
-- statement:
--   All gamma moment Fourier aliases at period 32 have total norm at most 2e-31, uniformly for every factorial-normalized moment, center T between 3 and 4 billion, and wanted frequency between 0 and 5. Proves the explicit contour constant and both infinite geometric tails. This is an analytic FFT error estimate, not the endpoint-sign or zero-count proof.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI 10.1090/mcom/3198, Poisson/gamma moment architecture. Ordinary Lean bounds using contour rotation, Cauchy and explicit geometric sums. Surrounding mathematical attribution: sometik179, c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_frequency_alias_bound :
  ∀ (T x : ℝ) (k : Nat), 3000000000≤T → T≤4000000000 → 0≤x → x≤5 →
  let φ : ℝ→ℂ := fun u => (Complex.Gamma (1/4+(((u+T)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp ((Real.pi*(u+T)/4-u^2/(2*(20:ℝ)^2):ℝ):ℂ)*
      (-2*(Real.pi:ℂ)*Complex.I*(u:ℂ))^k)/((k.factorial:ℂ)*(512:ℂ)^k)
  (∑' n : Nat, ‖𝓕 φ (x+32*(n+1:ℝ))‖)+
    (∑' n : Nat, ‖𝓕 φ (x-32*(n+1:ℝ))‖)≤2/10^31 := by sorry
