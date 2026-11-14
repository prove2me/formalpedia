-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_row23_low_zero_reciprocal_sum_20261114
-- name    : TaoFivePrimes.dusart_row23_low_zero_reciprocal_sum_20261114
-- status  : Open
-- author  : @abcdefg
-- created : 2026-11-13T22:01:18.350236+00:00
-- url     : https://prove2.me/theorems/57b11615-bf39-4863-8730-e202df03a140
-- title:
--   Row 23: low-zero reciprocal sum
-- statement:
--   For every finite set of nontrivial zeta zeros of positive imaginary part at most 1000, the sum of multiplicity divided by imaginary part is at most 2.028657. This is the precise open low-zero input used in the row-23 reduction.
-- source:
--   Derived zero estimate required by the formalized Dusart Table 1 row b=23 reduction; P. Dusart, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
open Complex DusartSmoothing
noncomputable section

theorem TaoFivePrimes.dusart_row23_low_zero_reciprocal_sum_20261114 : ∀ W : Finset ℂ,
  (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
  (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ) := by sorry
