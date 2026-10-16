-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_actual_to_proxy_fourier_error
-- name    : TaoFivePrimes.rh_fast_actual_to_proxy_fourier_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:55:21.223674+00:00
-- url     : https://prove2.me/theorems/960c091f-097d-4fc7-be30-8bc01ccfcd82
-- title:
--   TaoFivePrimes.rh_fast_actual_to_proxy_fourier_error
-- statement:
--   For every natural center3000000256<=T<=3300000000, every normalized-moment order and every real frequency, the true Gamma-window moment transform differs from the center-polynomial proxy transform by at most5e-16. Numerical evaluation and the complete RH window remain separate obligations.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Fourier.FourierTransform
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_actual_to_proxy_fourier_error (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (x:ℝ) :
 ‖𝓕 (fun t:ℝ=>Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*((T:ℝ)+t)/4-t^2/800:ℝ):ℂ))*RHFastGaussianWindow.momentFactor k t) x-
 𝓕 (RHFastGaussianWindow.momentProxy T k) x‖≤1/(2*10^15) := by sorry
