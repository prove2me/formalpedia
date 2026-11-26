-- Prove2me | Theorems.Thm_QuarterSumLadder_even_even_eight
-- name    : QuarterSumLadder.even_even_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:55.58639+00:00
-- url     : https://prove2.me/theorems/9db99625-2463-4f50-b47a-c48e83441fd2
-- title:
--   Quarter Sum Ladder: even even eight
-- statement:
--   For even `x, y`: `4 ∣ x² + y²`, and `8 ∣ x² + y² ↔ 4 ∣ x - y`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L44-L49
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L44-L49

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.even_even_eight {x y : ℤ} (hx : x % 2 = 0) (hy : y % 2 = 0) :
    (4 : ℤ) ∣ x ^ 2 + y ^ 2 ∧ ((8 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (4 : ℤ) ∣ x - y) := by sorry
