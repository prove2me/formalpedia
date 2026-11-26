-- Prove2me | Theorems.Thm_QuarterSumLadder_quadraticChar_of_char_gi
-- name    : QuarterSumLadder.quadraticChar_of_char_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:07.473008+00:00
-- url     : https://prove2.me/theorems/9483aeb5-5196-459b-9a2f-6a88c7de30fc
-- title:
--   Quarter Sum Ladder: quadratic Char of char gi
-- statement:
--   The Quarter Sum Ladder construction uses the quadratic Char of char gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L251-L254
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L251-L254

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

theorem QuarterSumLadder.quadraticChar_of_char_gi {x : ZMod p} (hx : x ≠ 0) (h : χ x = gi ∨ χ x = -gi) :
    quadraticChar (ZMod p) x = -1 := by sorry
