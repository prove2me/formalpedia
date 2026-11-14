-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_row23_remaining_low_rh_20261114
-- name    : TaoFivePrimes.dusart_row23_remaining_low_rh_20261114
-- status  : Open
-- author  : @abcdefg
-- created : 2026-11-13T22:01:36.523098+00:00
-- url     : https://prove2.me/theorems/2d298945-da81-44d5-b922-214db479ece7
-- title:
--   Row 23: remaining low-height RH intervals
-- statement:
--   Every nontrivial zeta zero whose absolute imaginary part lies in either (7,14) or (100, 121−5773/100000] has real part 1/2. This is the low-height RH input remaining after the locally checked zero-free and RH certificates.
-- source:
--   Derived zero estimate required by the formalized Dusart Table 1 row b=23 reduction; P. Dusart, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
open Complex DusartSmoothing
noncomputable section

theorem TaoFivePrimes.dusart_row23_remaining_low_rh_20261114 : ∀ ρ : NontrivialZetaZero,
  (((224/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
   ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) → ρ.val.re = 1/2 := by sorry
