-- Prove2me | Theorems.Thm_QuarterSumLadder_gi_pow_eq_one_iff
-- name    : QuarterSumLadder.gi_pow_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:06.992142+00:00
-- url     : https://prove2.me/theorems/b727d335-a3ad-5ae1-add4-6cf776069a3e
-- title:
--   Quarter Sum Ladder: gi pow eq one iff
-- statement:
--   The Quarter Sum Ladder construction uses the gi pow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L266-L273
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L266-L273

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hp hχ

theorem QuarterSumLadder.gi_pow_eq_one_iff {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ j = 1 ↔ 4 ∣ j := by sorry
