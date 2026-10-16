-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_all_gamma_fourier_enclosures
-- name    : TaoFivePrimes.rh_high_height_all_gamma_fourier_enclosures
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T12:50:35.789057+00:00
-- url     : https://prove2.me/theorems/188c72c1-5560-42c3-a8be-faae372886a5
-- title:
--   TaoFivePrimes.rh_high_height_all_gamma_fourier_enclosures
-- statement:
--   Assembles all24 accepted gamma moment Fourier enclosures into one indexed result, with the actual Fourier sample norm bounded by65537. The magnitude bound follows from accepted component bounds and the signed2^85 scaling. No zeta Fourier coefficient, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_all_gamma_fourier_enclosures (k j : Nat) (hk:k<24) (hj:j<1954) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537 := by sorry
