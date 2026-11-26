-- Prove2me | Theorems.Thm_QuarterSumLadder_sq_odd_mod_eight
-- name    : QuarterSumLadder.sq_odd_mod_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:28.117395+00:00
-- url     : https://prove2.me/theorems/905635f0-0971-4457-b031-f0076f595334
-- title:
--   Quarter Sum Ladder: sq odd mod eight
-- statement:
--   The Quarter Sum Ladder construction uses the sq odd mod eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L24-L28
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L24-L28

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.sq_odd_mod_eight {a : ℤ} (ha : a % 2 = 1) : a ^ 2 % 8 = 1 := by sorry
