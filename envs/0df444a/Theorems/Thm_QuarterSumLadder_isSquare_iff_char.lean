-- Prove2me | Theorems.Thm_QuarterSumLadder_isSquare_iff_char
-- name    : QuarterSumLadder.isSquare_iff_char
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:28.0939+00:00
-- url     : https://prove2.me/theorems/65619101-4d2c-42aa-8b45-5b3c1dc55e44
-- title:
--   Quarter Sum Ladder: is Square iff char
-- statement:
--   A nonzero `x` is a square exactly when `χ(x) = ± 1`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L223-L245
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L223-L245

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

theorem QuarterSumLadder.isSquare_iff_char {x : ZMod p} (hx : x ≠ 0) : IsSquare x ↔ (χ x = 1 ∨ χ x = -1) := by sorry
