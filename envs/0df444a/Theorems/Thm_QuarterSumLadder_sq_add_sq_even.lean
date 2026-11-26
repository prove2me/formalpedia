-- Prove2me | Theorems.Thm_QuarterSumLadder_sq_add_sq_even
-- name    : QuarterSumLadder.sq_add_sq_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:40.362634+00:00
-- url     : https://prove2.me/theorems/bba65a54-65f7-4e58-b226-b3cac13cb007
-- title:
--   Quarter Sum Ladder: sq add sq even
-- statement:
--   For even `x, y`: `x² + y² = 4((x/2)² + (y/2)²)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L37-L41
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L37-L41

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.sq_add_sq_even {x y : ℤ} (hx : x % 2 = 0) (hy : y % 2 = 0) :
    x ^ 2 + y ^ 2 = 4 * ((x / 2) ^ 2 + (y / 2) ^ 2) := by sorry
