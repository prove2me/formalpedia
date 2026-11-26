-- Prove2me | Theorems.Thm_QuarterSumLadder_gi_ne_one
-- name    : QuarterSumLadder.gi_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:27.866888+00:00
-- url     : https://prove2.me/theorems/202827a3-a306-5ddc-a16d-dab268e3efb6
-- title:
--   Quarter Sum Ladder: gi ne one
-- statement:
--   The Quarter Sum Ladder construction uses the gi ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L34-L35
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L34-L35

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.gi_ne_one : gi ≠ 1 := by sorry
