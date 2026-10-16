-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_gaussian_polynomial_fourier
-- name    : TaoFivePrimes.rh_fast_gaussian_polynomial_fourier
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:54:01.014444+00:00
-- url     : https://prove2.me/theorems/2aac0144-64c6-4eca-a416-fbad219bafca
-- title:
--   TaoFivePrimes.rh_fast_gaussian_polynomial_fourier
-- statement:
--   Exact Fourier transform of every monomial times a modulated Gaussian, for all positive widths and real modulations/frequencies. The result uses the probabilists Hermite polynomial. No approximation error, numerical table, zero count or RH interval is asserted.
-- source:
--   Gaussian integral and probabilists Hermite identities; center expansion of the first-correction Stirling exponent. Application under investigation: Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding mathematical attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_gaussian_polynomial_fourier (h ω x:ℝ) (hh:0<h) (n:Nat) :
  𝓕 (fun t:ℝ=>(t:ℂ)^n*Complex.exp (-(t:ℂ)^2/(2*(h:ℂ)^2)+
    Complex.I*(ω:ℂ)*t)) x=
    (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*(-Complex.I*(h:ℂ))^n*
      Polynomial.aeval (((h*(2*Real.pi*x-ω):ℝ):ℂ)) (Polynomial.hermite n)*
      Complex.exp (-(((h*(2*Real.pi*x-ω):ℝ):ℂ)^2)/2) := by sorry
