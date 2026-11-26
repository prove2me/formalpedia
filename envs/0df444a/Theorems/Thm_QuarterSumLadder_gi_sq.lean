-- Prove2me | Theorems.Thm_QuarterSumLadder_gi_sq
-- name    : QuarterSumLadder.gi_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:36.443878+00:00
-- url     : https://prove2.me/theorems/095b4772-e04f-598f-998f-fc2c808e344d
-- title:
--   Quarter Sum Ladder: gi sq
-- statement:
--   The Quarter Sum Ladder construction uses the gi sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L28-L29
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L28-L29

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.gi_sq : gi ^ 2 = -1 := by sorry
