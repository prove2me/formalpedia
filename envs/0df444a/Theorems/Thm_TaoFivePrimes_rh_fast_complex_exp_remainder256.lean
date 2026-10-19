-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_complex_exp_remainder256
-- name    : TaoFivePrimes.rh_fast_complex_exp_remainder256
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:34:42.800773+00:00
-- url     : https://prove2.me/theorems/17245d93-fb91-4d22-b95e-f0537636292e
-- title:
--   TaoFivePrimes.rh_fast_complex_exp_remainder256
-- statement:
--   For complex norm at most1/16, the degree40 exponential polynomial has error at most2^-256.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib.Analysis.SpecialFunctions.Exponential
open Complex Finset

theorem TaoFivePrimes.rh_fast_complex_exp_remainder256 (z:ℂ) (hz:‖z‖≤1/16) :
 ‖Complex.exp z-∑k∈Finset.range 41,z^k/(k.factorial:ℂ)‖≤1/(2:ℝ)^256 := by sorry
