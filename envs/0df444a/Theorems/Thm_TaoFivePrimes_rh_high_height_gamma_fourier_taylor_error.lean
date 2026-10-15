-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_taylor_error
-- name    : TaoFivePrimes.rh_high_height_gamma_fourier_taylor_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T20:39:34.322452+00:00
-- url     : https://prove2.me/theorems/73cc6718-a104-4737-8210-c44519f7874c
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fourier_taylor_error
-- statement:
--   For Gaussian width h=20, a shifted gamma Fourier transform is approximated by its first 20 moment transforms with absolute error <=10^-15 whenever |delta|<=1/1024. Uniform in height centre T and Fourier frequency x. This proves the finite Taylor truncation ingredient for the A=32, B=512 high-height evaluator, not its sampling aliases, arithmetic, or RH window.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI 10.1090/mcom/3198, Fourier/Taylor evaluation architecture. Ordinary Lean factorial Taylor remainder and conservative Gaussian moment envelope, using the accepted scaled Gamma bound 6. Original surrounding attribution: sometik179, c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_fourier_taylor_error :
  ∀ (T δ x : ℝ), |δ|≤1/1024 →
  let g : ℝ→ℂ := fun t => Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp ((Real.pi*(t+T)/4-t^2/(2*(20:ℝ)^2):ℝ):ℂ)
  ‖𝓕 g (x+δ)-∑ k ∈ Finset.range 20, ((δ:ℂ)^k/(k.factorial:ℂ))*
    𝓕 (fun t : ℝ => g t*(-2*(Real.pi:ℂ)*Complex.I*(t:ℂ))^k) x‖≤1/10^15 := by sorry
