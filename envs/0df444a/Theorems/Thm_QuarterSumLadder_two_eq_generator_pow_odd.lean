-- Prove2me | Theorems.Thm_QuarterSumLadder_two_eq_generator_pow_odd
-- name    : QuarterSumLadder.two_eq_generator_pow_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:43.161106+00:00
-- url     : https://prove2.me/theorems/6667d233-e22d-534e-9edd-cfea82821643
-- title:
--   Quarter Sum Ladder: two eq generator pow odd
-- statement:
--   `2` is an odd power of any generator when `p ≡ 5 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L187-L204
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L187-L204

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

theorem QuarterSumLadder.two_eq_generator_pow_odd (hp8 : p % 8 = 5) {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    ∃ e : ℕ, Odd e ∧ ((g ^ e : (ZMod p)ˣ) : ZMod p) = 2 := by sorry
