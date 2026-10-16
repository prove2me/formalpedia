-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_log_ratio_polynomial
-- name    : TaoFivePrimes.rh_fast_log_ratio_polynomial
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:59:54.541552+00:00
-- url     : https://prove2.me/theorems/4530bb11-5545-4abe-8770-739841dbcf0c
-- title:
--   TaoFivePrimes.rh_fast_log_ratio_polynomial
-- statement:
--   For0<=x<=1/3, the64-term odd logarithm polynomial approximates log((1+x)/(1-x)) within2^-128 in complex norm. Integer Horner evaluation and concrete logarithm seeds require separate proofs.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

theorem TaoFivePrimes.rh_fast_log_ratio_polynomial (x:ℝ) (hx0:0≤x) (hx:x≤1/3) :
 ‖((Real.log ((1+x)/(1-x)):ℝ):ℂ)-
   2*(x:ℂ)*(∑k∈Finset.range 64,(x:ℂ)^(2*k)/((2*k+1:Nat):ℂ))‖≤1/(2:ℝ)^128 := by sorry
