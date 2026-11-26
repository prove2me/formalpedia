-- Prove2me | Theorems.Thm_QuarterSumLadder_unit_apply_pow_four
-- name    : QuarterSumLadder.unit_apply_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:07.772927+00:00
-- url     : https://prove2.me/theorems/2dd7a21c-828a-5320-8967-7cd808a62309
-- title:
--   Quarter Sum Ladder: unit apply pow four
-- statement:
--   The Quarter Sum Ladder construction uses the unit apply pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L90-L92
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L90-L92

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

theorem QuarterSumLadder.unit_apply_pow_four {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 4)
    (u : (ZMod p)ˣ) : χ u ^ 4 = 1 := by sorry
