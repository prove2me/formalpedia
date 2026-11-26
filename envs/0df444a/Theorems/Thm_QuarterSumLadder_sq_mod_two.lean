-- Prove2me | Theorems.Thm_QuarterSumLadder_sq_mod_two
-- name    : QuarterSumLadder.sq_mod_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:01.307123+00:00
-- url     : https://prove2.me/theorems/4d140453-568f-49d4-9689-20c5d6b7a2ba
-- title:
--   Quarter Sum Ladder: sq mod two
-- statement:
--   The Quarter Sum Ladder construction uses the sq mod two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L17-L22
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L17-L22

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.sq_mod_two (a : ℤ) : a ^ 2 % 2 = a % 2 := by sorry
