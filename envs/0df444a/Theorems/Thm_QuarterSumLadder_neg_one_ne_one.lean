-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_one_ne_one
-- name    : QuarterSumLadder.neg_one_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:48.834253+00:00
-- url     : https://prove2.me/theorems/81930eec-f896-496c-9387-4ab3f1633709
-- title:
--   Quarter Sum Ladder: neg one ne one
-- statement:
--   The Quarter Sum Ladder construction uses the neg one ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L40-L41
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L40-L41

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.neg_one_ne_one : (-1 : GaussianInt) ≠ 1 := by sorry
