-- Prove2me | Theorems.Thm_QuarterSumLadder_quartic_apply_neg_one_of_one
-- name    : QuarterSumLadder.quartic_apply_neg_one_of_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:07.507863+00:00
-- url     : https://prove2.me/theorems/c76e5b45-07b8-5f0c-8e01-ea9ce9c51318
-- title:
--   Quarter Sum Ladder: quartic apply neg one of one
-- statement:
--   **Proposition 1.1, order four, converse.** For `p ≡ 1 (mod 8)` a quartic character is even.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L177-L183
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L177-L183

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
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ

theorem QuarterSumLadder.quartic_apply_neg_one_of_one (hp8 : p % 8 = 1) : χ (-1) = 1 := by sorry
