-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_row23_if_rh380k_and_low_sum_20261114
-- name    : TaoFivePrimes.dusart_row23_if_rh380k_and_low_sum_20261114
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-13T22:36:28.502484+00:00
-- url     : https://prove2.me/theorems/ff9fefed-231b-4c06-ad24-6269d5d89ab3
-- title:
--   Row 23 psi bound from RH through 380000 and a low-zero sum
-- statement:
--   Assume that every nontrivial zeta zero with absolute imaginary part at most 380000 lies on the critical line and that the multiplicity-weighted reciprocal sum for positive zeros through height 1000 is at most 2.028657. Then for every real $x\ge e^{23}$ the Chebyshev psi function satisfies $|\psi(x)-x|\le0.0002431x$. Both hypotheses are explicit assumptions.
-- source:
--   Conditional reduction for the b=23 row of P. Dusart, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
open Complex DusartSmoothing
noncomputable section

theorem TaoFivePrimes.dusart_row23_if_rh380k_and_low_sum_20261114
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hRH : ∀ ρ : NontrivialZetaZero, |ρ.val.im| ≤ (380000:ℝ) → ρ.val.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ) * x := by sorry
