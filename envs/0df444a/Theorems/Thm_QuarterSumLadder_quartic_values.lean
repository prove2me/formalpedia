-- Prove2me | Theorems.Thm_QuarterSumLadder_quartic_values
-- name    : QuarterSumLadder.quartic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:48.783551+00:00
-- url     : https://prove2.me/theorems/5cd78bbd-5563-5fb8-a4a3-4fd0b6276a74
-- title:
--   Quarter Sum Ladder: quartic values
-- statement:
--   Nonzero values of a quartic character are fourth roots of unity.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L123-L125
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L123-L125

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

theorem QuarterSumLadder.quartic_values {a : ZMod p} (ha : a ≠ 0) :
    χ a = 1 ∨ χ a = gi ∨ χ a = -1 ∨ χ a = -gi := by sorry
