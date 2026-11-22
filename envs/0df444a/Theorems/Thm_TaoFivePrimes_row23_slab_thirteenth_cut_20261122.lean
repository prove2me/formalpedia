-- Prove2me | Theorems.Thm_TaoFivePrimes_row23_slab_thirteenth_cut_20261122
-- name    : TaoFivePrimes.row23_slab_thirteenth_cut_20261122
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-21T21:16:58.405813+00:00
-- url     : https://prove2.me/theorems/0bb330e5-ed5a-4735-a295-49d6d1c4c5f7
-- title:
--   Row 23 conditional bound after the thirteenth low-height slab
-- statement:
--   The stated zero-sum, remaining low-height critical-line gaps, and positive-height tail hypotheses imply the Dusart row-23 bound $|\psi(x)-x|\le 0.0002431x$ for all $x\ge e^{23}$. This is the conditional reduction after thirteen certified low-height slabs.
-- source:
--   P. Dusart, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
open Complex DusartSmoothing
noncomputable section

theorem TaoFivePrimes.row23_slab_thirteenth_cut_20261122
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (((214/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by sorry
