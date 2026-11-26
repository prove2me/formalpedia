-- Prove2me | Theorems.Thm_QuarterSumLadder_apply_neg_one_of_odd_orderOf
-- name    : QuarterSumLadder.apply_neg_one_of_odd_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:50.981477+00:00
-- url     : https://prove2.me/theorems/f986bf72-11b7-49fd-8c58-ff7b82c6ccc1
-- title:
--   Quarter Sum Ladder: apply neg one of odd order Of
-- statement:
--   **Proposition 1.1, odd orders.** A character of odd order is even.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L95-L103
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L95-L103

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

theorem QuarterSumLadder.apply_neg_one_of_odd_orderOf {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (h : Odd (orderOf χ)) : χ (-1) = 1 := by sorry
