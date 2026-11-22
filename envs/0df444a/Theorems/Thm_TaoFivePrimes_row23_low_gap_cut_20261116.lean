-- Prove2me | Theorems.Thm_TaoFivePrimes_row23_low_gap_cut_20261116
-- name    : TaoFivePrimes.row23_low_gap_cut_20261116
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-21T20:14:07.710057+00:00
-- url     : https://prove2.me/theorems/f9bbf11d-8251-4a10-8e8b-d83e7a2de6ed
-- title:
--   Row 23 conditional psi bound from low-height gaps
-- statement:
--   Assuming the stated reciprocal-zero sum, the two stated low-height critical-line intervals, and the stated positive-height critical-line tail, the Chebyshev psi function satisfies $|\psi(x)-x|\le 0.0002431x$ for every $x\ge e^{23}$. This is an intermediate reduction with its assumptions retained.
-- source:
--   P. Dusart, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
open Complex DusartSmoothing
noncomputable section

theorem TaoFivePrimes.row23_low_gap_cut_20261116
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (|ρ.val.im| < (14:ℝ) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by sorry
