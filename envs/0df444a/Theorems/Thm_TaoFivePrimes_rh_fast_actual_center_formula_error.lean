-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_actual_center_formula_error
-- name    : TaoFivePrimes.rh_fast_actual_center_formula_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:08:51.11709+00:00
-- url     : https://prove2.me/theorems/8e2f011a-bff5-4374-a0f2-7aad172fd65c
-- title:
--   TaoFivePrimes.rh_fast_actual_center_formula_error
-- statement:
--   For every natural center3000000256<=T<=3300000000, every normalized-moment order and every real frequency, the true moment transform in the existing sampling interface differs from the short29-term center formula by at most5e-16. Rounded evaluation and a complete RH window remain separate.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Mathlib.Analysis.Fourier.FourierTransform
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_actual_center_formula_error (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (x:ℝ) :
 ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) x-RHFastGaussianWindow.fourierFormula T k x‖≤1/(2*10^15) := by sorry
