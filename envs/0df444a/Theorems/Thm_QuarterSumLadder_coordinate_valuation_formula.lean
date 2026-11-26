-- Prove2me | Theorems.Thm_QuarterSumLadder_coordinate_valuation_formula
-- name    : QuarterSumLadder.coordinate_valuation_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:56.924812+00:00
-- url     : https://prove2.me/theorems/9f0e83a6-0383-41dc-9624-91983d3e4074
-- title:
--   Quarter Sum Ladder: coordinate valuation formula
-- statement:
--   **The coordinate valuation** (Paper IV, Lemma 5.5): for `x, y ≠ 0`,
--   `v₂(x² + y²) = 2 min(v₂ x, v₂ y) + [v₂ x = v₂ y]`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L144-L148
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L144-L148

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.coordinate_valuation_formula {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValInt 2 (x ^ 2 + y ^ 2) =
      2 * min (padicValInt 2 x) (padicValInt 2 y) +
        if padicValInt 2 x = padicValInt 2 y then 1 else 0 := by sorry
