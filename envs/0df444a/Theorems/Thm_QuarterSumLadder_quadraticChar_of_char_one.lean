-- Prove2me | Theorems.Thm_QuarterSumLadder_quadraticChar_of_char_one
-- name    : QuarterSumLadder.quadraticChar_of_char_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:54.537665+00:00
-- url     : https://prove2.me/theorems/ee995b9f-2091-47d9-aaa4-92fdf8bb46ed
-- title:
--   Quarter Sum Ladder: quadratic Char of char one
-- statement:
--   The Quarter Sum Ladder construction uses the quadratic Char of char one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L247-L249
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L247-L249

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

theorem QuarterSumLadder.quadraticChar_of_char_one {x : ZMod p} (hx : x ≠ 0) (h : χ x = 1 ∨ χ x = -1) :
    quadraticChar (ZMod p) x = 1 := by sorry
