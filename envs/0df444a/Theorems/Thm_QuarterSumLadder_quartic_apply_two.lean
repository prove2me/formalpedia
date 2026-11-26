-- Prove2me | Theorems.Thm_QuarterSumLadder_quartic_apply_two
-- name    : QuarterSumLadder.quartic_apply_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:17.870977+00:00
-- url     : https://prove2.me/theorems/f4d1a91a-47df-4df2-823f-14cf5ade4f6e
-- title:
--   Quarter Sum Ladder: quartic apply two
-- statement:
--   For `p ≡ 5 (mod 8)`, `χ 2 = ± i`: `2` is a quadratic non-residue.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L207-L211
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L207-L211

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

theorem QuarterSumLadder.quartic_apply_two (hp8 : p % 8 = 5) : χ 2 = gi ∨ χ 2 = -gi := by sorry
