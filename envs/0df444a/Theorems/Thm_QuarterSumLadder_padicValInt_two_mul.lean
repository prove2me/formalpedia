-- Prove2me | Theorems.Thm_QuarterSumLadder_padicValInt_two_mul
-- name    : QuarterSumLadder.padicValInt_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:32.427728+00:00
-- url     : https://prove2.me/theorems/300b515b-545f-4a74-941b-e6bd70ab85e8
-- title:
--   Quarter Sum Ladder: padic Val Int two mul
-- statement:
--   The Quarter Sum Ladder construction uses the padic Val Int two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L82-L83
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L82-L83

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.padicValInt_two_mul {a : ℤ} (ha : a ≠ 0) : padicValInt 2 (2 * a) = padicValInt 2 a + 1 := by sorry
