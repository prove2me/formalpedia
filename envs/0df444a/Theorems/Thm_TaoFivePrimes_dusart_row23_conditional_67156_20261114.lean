-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_row23_conditional_67156_20261114
-- name    : TaoFivePrimes.dusart_row23_conditional_67156_20261114
-- status  : Open
-- author  : @abcdefg
-- created : 2026-11-13T22:01:23.446971+00:00
-- url     : https://prove2.me/theorems/d49ac214-f62c-49e7-9be4-c1b71550c196
-- title:
--   Row 23 psi bound conditional on three zero estimates
-- statement:
--   Assume the explicit low-zero reciprocal-sum bound, the remaining low-height RH intervals, and the positive-height RH tail appearing in the formal statement. Then for every real $x\ge e^{23}$, the bound $|\psi(x)-x|\le 0.0002431x$ holds. A proof has been checked locally; its supporting Lean modules are being published. This theorem remains Open until its proof is accepted.
-- source:
--   Conditional reduction derived from P. Dusart, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
open Complex DusartSmoothing
noncomputable section

theorem TaoFivePrimes.dusart_row23_conditional_67156_20261114
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (((224/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (67156 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by sorry
