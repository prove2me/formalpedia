-- Prove2me | Theorems.Thm_QuarterSumLadder_quartic_apply_neg_one
-- name    : QuarterSumLadder.quartic_apply_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:04.456015+00:00
-- url     : https://prove2.me/theorems/94c989b3-1d1d-582a-ab1b-dd454aa9aad0
-- title:
--   Quarter Sum Ladder: quartic apply neg one
-- statement:
--   **Proposition 1.1, order four.** For `p ≡ 5 (mod 8)` a quartic character is odd.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L168-L174
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L168-L174

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

theorem QuarterSumLadder.quartic_apply_neg_one (hp8 : p % 8 = 5) : χ (-1) = -1 := by sorry
