-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_one_eq_generator_pow
-- name    : QuarterSumLadder.neg_one_eq_generator_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:18.360307+00:00
-- url     : https://prove2.me/theorems/18a4a0d5-c60f-41e3-980d-0cef0346a7e4
-- title:
--   Quarter Sum Ladder: neg one eq generator pow
-- statement:
--   `-1 = g ^ ((p - 1) / 2)` for a generator `g`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L147-L165
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L147-L165

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
omit hχ

theorem QuarterSumLadder.neg_one_eq_generator_pow (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hgo : orderOf g = p - 1) :
    ((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) = -1 := by sorry
