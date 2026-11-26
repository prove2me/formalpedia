-- Prove2me | Theorems.Thm_QuarterSumLadder_gi_pow_four
-- name    : QuarterSumLadder.gi_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:30.129144+00:00
-- url     : https://prove2.me/theorems/ab252369-cf17-4876-a091-0258b71f2c76
-- title:
--   Quarter Sum Ladder: gi pow four
-- statement:
--   The Quarter Sum Ladder construction uses the gi pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L31-L32
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L31-L32

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.gi_pow_four : gi ^ 4 = 1 := by sorry
