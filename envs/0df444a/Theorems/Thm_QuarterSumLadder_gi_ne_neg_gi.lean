-- Prove2me | Theorems.Thm_QuarterSumLadder_gi_ne_neg_gi
-- name    : QuarterSumLadder.gi_ne_neg_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:45.063807+00:00
-- url     : https://prove2.me/theorems/0335a06a-c5eb-4c31-af83-e132d4107a93
-- title:
--   Quarter Sum Ladder: gi ne neg gi
-- statement:
--   The Quarter Sum Ladder construction uses the gi ne neg gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L37-L38
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L37-L38

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.gi_ne_neg_gi : gi ≠ -gi := by sorry
