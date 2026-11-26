-- Prove2me | Theorems.Thm_QuarterSumLadder_padicValInt_odd
-- name    : QuarterSumLadder.padicValInt_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:31.541716+00:00
-- url     : https://prove2.me/theorems/a4550256-0f7c-595c-9900-84788bfb2866
-- title:
--   Quarter Sum Ladder: padic Val Int odd
-- statement:
--   The Quarter Sum Ladder construction uses the padic Val Int odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L85-L86
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L85-L86

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.padicValInt_odd {a : ℤ} (ha : a % 2 = 1) : padicValInt 2 a = 0 := by sorry
