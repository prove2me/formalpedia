-- Prove2me | Theorems.Thm_QuarterSumLadder_pm_gi_pow_two_mul
-- name    : QuarterSumLadder.pm_gi_pow_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:57.370974+00:00
-- url     : https://prove2.me/theorems/76c1ff5a-d8c5-595d-8fe9-1d7e807990f6
-- title:
--   Quarter Sum Ladder: pm gi pow two mul
-- statement:
--   Even powers of `± i` are `(-1) ^ j`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L66-L69
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L66-L69

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.pm_gi_pow_two_mul {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ (2 * j) = (-1) ^ j := by sorry
