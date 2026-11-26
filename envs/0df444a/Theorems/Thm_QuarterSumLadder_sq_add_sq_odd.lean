-- Prove2me | Theorems.Thm_QuarterSumLadder_sq_add_sq_odd
-- name    : QuarterSumLadder.sq_add_sq_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:37.562796+00:00
-- url     : https://prove2.me/theorems/e7c96267-42a7-4607-9711-7d0ab3039e7c
-- title:
--   Quarter Sum Ladder: sq add sq odd
-- statement:
--   The Quarter Sum Ladder construction uses the sq add sq odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L30-L31
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L30-L31

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.sq_add_sq_odd {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1) : (x ^ 2 + y ^ 2) % 8 = 2 := by sorry
