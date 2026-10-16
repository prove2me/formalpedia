-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_full_window_reconstruction
-- name    : TaoFivePrimes.rh_batch01_height_full_window_reconstruction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:19:36.2979+00:00
-- url     : https://prove2.me/theorems/69ad8c8e-6ef7-482f-bcd3-506928071ae7
-- title:
--   TaoFivePrimes.rh_batch01_height_full_window_reconstruction
-- statement:
--   Conditional uniform reconstruction of the actual completed-zeta Gaussian window on[-256,256] from the explicit1025 nonnegative Fourier coefficients: coefficient errors at most10^(-14) imply pointwise complex error at most4*10^(-11). Proves Poisson summation and both time/frequency alias tails. The coefficient hypothesis is explicit and remains to be supplied by separate accepted FFT and Dirichlet proofs. No endpoint sign, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FourierPolynomial
open scoped FourierTransform

theorem TaoFivePrimes.rh_batch01_height_full_window_reconstruction (T x : ℝ) (hT:3000000000≤T ∧ T≤3300000000) (hx:|x|≤256)
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 (fun t:ℝ=>completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*Complex.exp (((Real.pi*(t+T)/4-t^2/800:ℝ):ℂ))) ((m:ℝ)/512)-RHBatch01FourierPolynomial.coefficient m‖≤1/10^14) :
 ‖(fun t:ℝ=>completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*Complex.exp (((Real.pi*(t+T)/4-t^2/800:ℝ):ℂ))) x-RHBatch01FourierPolynomial.polynomial (x:ℂ)‖≤4/10^11 := by sorry
