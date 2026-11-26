-- Prove2me | Theorems.Thm_QuarterSumLadder_eq_of_pow_four_eq_one
-- name    : QuarterSumLadder.eq_of_pow_four_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:57.39318+00:00
-- url     : https://prove2.me/theorems/0b5d4a8a-35d3-4deb-8cf4-6a88a3cddb8a
-- title:
--   Quarter Sum Ladder: eq of pow four eq one
-- statement:
--   The fourth roots of unity in `ℤ[i]` are `1, i, -1, -i`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L44-L54
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L44-L54

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.eq_of_pow_four_eq_one {x : GaussianInt} (h : x ^ 4 = 1) :
    x = 1 ∨ x = gi ∨ x = -1 ∨ x = -gi := by sorry
