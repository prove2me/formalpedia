-- Prove2me | Theorems.Thm_QuarterSumLadder_apply_of_orderOf_two
-- name    : QuarterSumLadder.apply_of_orderOf_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:08.129334+00:00
-- url     : https://prove2.me/theorems/5ac8b1dd-ab3f-4502-965a-8048d4eded67
-- title:
--   Quarter Sum Ladder: apply of order Of two
-- statement:
--   **Proposition 1.1, order two.** A character of order two is real: its values are
--   `0` and `± 1`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L107-L115
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L107-L115

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

theorem QuarterSumLadder.apply_of_orderOf_two (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 2)
    (a : ZMod p) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by sorry
