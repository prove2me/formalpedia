-- Prove2me | Theorems.Thm_QuarterSumLadder_quadraticChar_eq_sq
-- name    : QuarterSumLadder.quadraticChar_eq_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:20.091656+00:00
-- url     : https://prove2.me/theorems/2baf8d6e-9a58-5954-911e-7add6e219f9e
-- title:
--   Quarter Sum Ladder: quadratic Char eq sq
-- statement:
--   `(n/p) = χ(n)²` for `n ≠ 0`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L257-L263
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L257-L263

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

theorem QuarterSumLadder.quadraticChar_eq_sq {n : ZMod p} (hn : n ≠ 0) :
    ((quadraticChar (ZMod p) n : ℤ) : GaussianInt) = χ n ^ 2 := by sorry
