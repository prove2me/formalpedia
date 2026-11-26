-- Prove2me | Theorems.Thm_QuarterSumLadder_sq_add_sq_mixed
-- name    : QuarterSumLadder.sq_add_sq_mixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:37.61245+00:00
-- url     : https://prove2.me/theorems/479fa7dc-f9b0-5b16-98ea-89cccc1f70ed
-- title:
--   Quarter Sum Ladder: sq add sq mixed
-- statement:
--   The Quarter Sum Ladder construction uses the sq add sq mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L33-L34
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L33-L34

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.sq_add_sq_mixed {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 0) : (x ^ 2 + y ^ 2) % 2 = 1 := by sorry
