-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_coefficient_from_gamma_bounds
-- name    : TaoFivePrimes.rh_fast_window256_coefficient_from_gamma_bounds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:21:47.607629+00:00
-- url     : https://prove2.me/theorems/ab120930-348f-4780-a7cb-b4af1016c9a7
-- title:
--   TaoFivePrimes.rh_fast_window256_coefficient_from_gamma_bounds
-- statement:
--   Explicit1e-15 true Gamma moment enclosures imply1e-14 accuracy of all1025 window Fourier coefficients. The Gamma enclosures remain a hypothesis and no old numerical Gamma accuracy certificate is used.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_window256_coefficient_from_gamma_bounds
 (hgamma:∀k j:Nat,k<24 → j<1954 →
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537)
 (m : Nat) (hm:m≤1024) :
 ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14 := by sorry
