-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_frequency_enclosure_from_checked
-- name    : TaoFivePrimes.rh_fast_window256_frequency_enclosure_from_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:19:51.282004+00:00
-- url     : https://prove2.me/theorems/5f4ba8d4-24fb-4950-8393-df0dc72f01eb
-- title:
--   TaoFivePrimes.rh_fast_window256_frequency_enclosure_from_checked
-- statement:
--   At every checked frequency j/512 with j<1954, all24 true normalized Gamma moment transforms are within1e-15 of the original proposed table, and have norm at most65537.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_window256_frequency_enclosure_from_checked (k j:Nat) (hk:k<24) (hj:j<1954)
 (hchecked:RHFastWindow256CompactReference.checked j=true) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537 := by sorry
