-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_new256_frequency_enclosure_from_checked
-- name    : TaoFivePrimes.rh_batch01_new256_frequency_enclosure_from_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T16:06:28.671377+00:00
-- url     : https://prove2.me/theorems/6cbb377a-3f44-4a72-be44-02fa76dd94b8
-- title:
--   TaoFivePrimes.rh_batch01_new256_frequency_enclosure_from_checked
-- statement:
--   Ordinary proof of the fresh-center frequency enclosure from checked. Numerical arithmetic remains a separate required input.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original mathematical attribution: sometik179, submission c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_setup_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_frequency_checker_soundness256
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_packed_reference_lookup
import Theorems.Thm_TaoFivePrimes_rh_fast_actual_center_formula_error
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open Complex
open scoped FourierTransform

theorem TaoFivePrimes.rh_batch01_new256_frequency_enclosure_from_checked (k j:Nat) (hk:k<24) (hj:j<1954)
 (hchecked:RHBatch01New256CompactReference.checked j=true) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)-RHBatch01GammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)‖≤65537 := by sorry
