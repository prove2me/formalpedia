-- Prove2me | Theorems.Thm_QuarterSumLadder_char_eq_one_iff
-- name    : QuarterSumLadder.char_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:27.313949+00:00
-- url     : https://prove2.me/theorems/a16684a2-d8b9-5db1-b4cf-2adbb82f1b6b
-- title:
--   Quarter Sum Ladder: char eq one iff
-- statement:
--   `χ(n) = 1` exactly when `n` is a nonzero fourth power.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L276-L291
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L276-L291

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

theorem QuarterSumLadder.char_eq_one_iff {n : ZMod p} (hn : n ≠ 0) : χ n = 1 ↔ ∃ y : ZMod p, y ^ 4 = n := by sorry
