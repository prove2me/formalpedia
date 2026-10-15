-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_time_alias_bound
-- name    : TaoFivePrimes.rh_high_height_gamma_time_alias_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T20:58:32.273336+00:00
-- url     : https://prove2.me/theorems/a2bd9633-e70d-4e0b-90f3-fe5c155dfbe2
-- title:
--   TaoFivePrimes.rh_high_height_gamma_time_alias_bound
-- statement:
--   For Gaussian width h=20 and period B=512, the sum of norms of both noncentral time aliases of every factorial-normalized gamma moment is at most 10^-18 for grid coordinates in [-256,256]. Uniform in height centre T and moment degree k. This is one quantitative sampling ingredient, not a proof of the FFT arithmetic or the RH window.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI 10.1090/mcom/3198, Gaussian moment/Poisson sampling architecture. Conservative ordinary Lean derivation from the accepted scaled Gamma bound, the exponential-series term bound, quadratic tails, and a geometric sum. Original surrounding attribution: sometik179, c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound

theorem TaoFivePrimes.rh_high_height_gamma_time_alias_bound :
  ∀ (T t : ℝ) (k : Nat), -256≤t → t≤256 →
  let φ : ℝ→ℂ := fun u => (Complex.Gamma (1/4+(((u+T)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp ((Real.pi*(u+T)/4-u^2/(2*(20:ℝ)^2):ℝ):ℂ)*
      (-2*(Real.pi:ℂ)*Complex.I*(u:ℂ))^k)/((k.factorial:ℂ)*(512:ℂ)^k)
  (∑' n : Nat, ‖φ (t+(n+1:ℝ)*512)‖)+(∑' n : Nat, ‖φ (t-(n+1:ℝ)*512)‖)≤1/10^18 := by sorry
