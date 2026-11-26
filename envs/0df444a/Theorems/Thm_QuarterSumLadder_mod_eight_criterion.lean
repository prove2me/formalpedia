-- Prove2me | Theorems.Thm_QuarterSumLadder_mod_eight_criterion
-- name    : QuarterSumLadder.mod_eight_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:19.547913+00:00
-- url     : https://prove2.me/theorems/f6c9e6b7-dbde-4820-b3d8-8823e463e3ba
-- title:
--   Quarter Sum Ladder: mod eight criterion
-- statement:
--   **The mod-8 criterion** (Paper IV, Theorem 3.2): `8 ∣ c₀` and `8 ∣ c₁` exactly when
--   `χ(2) = 1`, that is, when `2` is a fourth power modulo `p`. (Gauss's criterion, `p = a² + 64 b²`, is
--   not formalized.)
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L251-L270
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L251-L270

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.mod_eight_criterion :
    ((8 : ℤ) ∣ c0 χ ∧ (8 : ℤ) ∣ c1 χ ↔ χ 2 = 1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) := by sorry
