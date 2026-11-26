-- Prove2me | Theorems.Thm_QuarterSumLadder_pm_gi_pow_odd
-- name    : QuarterSumLadder.pm_gi_pow_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:57.589494+00:00
-- url     : https://prove2.me/theorems/1bb46803-e920-4e9a-8520-dfa54f52c14d
-- title:
--   Quarter Sum Ladder: pm gi pow odd
-- statement:
--   Odd powers of `± i` are `± i`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L57-L63
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L57-L63

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.pm_gi_pow_odd {u : GaussianInt} (hu : u = gi ∨ u = -gi) {e : ℕ} (he : Odd e) :
    u ^ e = gi ∨ u ^ e = -gi := by sorry
