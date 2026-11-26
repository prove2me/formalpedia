-- Prove2me | Theorems.Thm_QuarterSumLadder_coordinate_valuation
-- name    : QuarterSumLadder.coordinate_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:27.531236+00:00
-- url     : https://prove2.me/theorems/68738043-ef45-56de-b0f0-b41d37295a02
-- title:
--   Quarter Sum Ladder: coordinate valuation
-- statement:
--   **The coordinate valuation** (Paper IV, Lemma 5.5): for `x, y ≠ 0`,
--   `v₂(x² + y²) = 2 min(v₂ x, v₂ y) + δ`, with `δ = 1` if `v₂ x = v₂ y` and `δ = 0` otherwise.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L90-L124
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L90-L124

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.coordinate_valuation {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValInt 2 (x ^ 2 + y ^ 2) =
      2 * min (padicValInt 2 x) (padicValInt 2 y) +
        if padicValInt 2 x = padicValInt 2 y then 1 else 0 := by sorry
