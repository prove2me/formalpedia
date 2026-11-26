-- Prove2me | Theorems.Thm_QuarterSumLadder_exists_generator
-- name    : QuarterSumLadder.exists_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:39.023218+00:00
-- url     : https://prove2.me/theorems/e424014d-76cd-5476-b6f7-82d96c32131e
-- title:
--   Quarter Sum Ladder: exists generator
-- statement:
--   A generator of `(ZMod p)ˣ`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L83-L88
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L83-L88

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

theorem QuarterSumLadder.exists_generator :
    ∃ g : (ZMod p)ˣ, orderOf g = p - 1 ∧ ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u := by sorry
