-- Prove2me | Theorems.Thm_QuarterSumLadder_quartic_apply_generator
-- name    : QuarterSumLadder.quartic_apply_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:44.445148+00:00
-- url     : https://prove2.me/theorems/b39a583b-2082-4023-9274-201f8f3942d9
-- title:
--   Quarter Sum Ladder: quartic apply generator
-- statement:
--   On a generator, a quartic character takes the value `± i`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L128-L143
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L128-L143

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

theorem QuarterSumLadder.quartic_apply_generator {g : (ZMod p)ˣ} (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    χ g = gi ∨ χ g = -gi := by sorry
