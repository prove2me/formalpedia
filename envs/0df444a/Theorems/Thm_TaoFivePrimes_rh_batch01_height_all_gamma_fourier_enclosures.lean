-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_all_gamma_fourier_enclosures
-- name    : TaoFivePrimes.rh_batch01_height_all_gamma_fourier_enclosures
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T18:03:24.015916+00:00
-- url     : https://prove2.me/theorems/4ccfb8b3-f353-474a-9e2f-ff9887d72779
-- title:
--   TaoFivePrimes.rh_batch01_height_all_gamma_fourier_enclosures
-- statement:
--   All actual fresh-center Gamma Fourier enclosures follow from the center/Gaussian/Hermite method, with independently checked seed and256-bit integer arithmetic. Old dense Gamma FFT accuracy proofs are not used.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
open scoped FourierTransform

theorem TaoFivePrimes.rh_batch01_height_all_gamma_fourier_enclosures (k j : Nat) (hk:k<24) (hj:j<1954) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)-RHBatch01GammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)‖≤65537 := by sorry
