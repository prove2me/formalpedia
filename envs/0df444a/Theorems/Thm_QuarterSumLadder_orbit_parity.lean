-- Prove2me | Theorems.Thm_QuarterSumLadder_orbit_parity
-- name    : QuarterSumLadder.orbit_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:58.161083+00:00
-- url     : https://prove2.me/theorems/3d848543-66d7-5db8-9c61-fc7f101cb2a6
-- title:
--   Quarter Sum Ladder: orbit parity
-- statement:
--   **Doubling-orbit parity** (Paper IV, Theorem 3.3). If `χ(2) = 1`, then
--   `R₀ ≡ R₁ ≡ R₂ ≡ R₃ (mod 2)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L225-L246
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L225-L246

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.orbit_parity (hw : χ 2 = 1) :
    R χ 1 % 2 = R χ 0 % 2 ∧ R χ 2 % 2 = R χ 0 % 2 ∧ R χ 3 % 2 = R χ 0 % 2 := by sorry
