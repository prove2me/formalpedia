-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_finite_dirichlet50000
-- name    : TaoFivePrimes.rh_high_height_finite_dirichlet50000
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:23:31.095976+00:00
-- url     : https://prove2.me/theorems/8cc1b551-094d-4c62-be25-b1315f2e16ce
-- title:
--   TaoFivePrimes.rh_high_height_finite_dirichlet50000
-- statement:
--   The actual completed-zeta Gaussian-window Fourier transform is enclosed by its first50000 explicitly shifted gamma-transform Dirichlet terms with complex error at most10^(-16), uniformly for3e9≤T≤3.3e9 and nonnegative frequencies. Proves pole corrections and the rigorously truncated Dirichlet tail. No endpoint sign, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_finite_dirichlet50000 (T x : ℝ) (hT:3000000000≤T ∧ T≤3300000000) (hx:0≤x) :
 let W:ℝ→ℂ:=fun t=>completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*
  Complex.exp (((Real.pi*(t+T)/4-t^2/800:ℝ):ℂ))
 ‖𝓕 W x-∑n∈Finset.range 50000,
  Complex.exp (-(1/2+Complex.I*(T:ℂ))*(Real.log ((n+1:ℝ)*Real.sqrt Real.pi):ℂ))*
  𝓕 (RHHighSamplingFunctions.gammaWindow T)
   (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi))‖≤1/10^16 := by sorry
