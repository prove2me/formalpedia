-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_taylor24
-- name    : TaoFivePrimes.rh_high_height_gamma_fourier_taylor24
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:19:11.112223+00:00
-- url     : https://prove2.me/theorems/42a34d1b-3fd9-40c0-83ca-69d14cfde108
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fourier_taylor24
-- statement:
--   Uniform24-term Taylor expansion of the actual gamma-window Fourier transform at a frequency offset at most1/1024. The coefficients are precisely the public normalized moment Fourier integrals, and the complex error is at most10^(-20), proved from the Gaussian integral remainder. No endpoint sign, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_fourier_taylor24 (T d x : ℝ) (hd:|d|≤1/2) :
 ‖𝓕 (RHHighSamplingFunctions.gammaWindow T) (x+d/512)-
   ∑k∈Finset.range 24,(d:ℂ)^k*𝓕 (RHHighSamplingFunctions.moment T k) x‖≤1/10^20 := by sorry
