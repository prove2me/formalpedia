-- Prove2me | Theorems.Thm_QuarterSumLadder_coords_mod_eight
-- name    : QuarterSumLadder.coords_mod_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:14.820889+00:00
-- url     : https://prove2.me/theorems/56e17d2b-13a4-5c0c-a252-13384b5d8abe
-- title:
--   Quarter Sum Ladder: coords mod eight
-- statement:
--   `c₀ ≡ c₁ ≡ 4(R₁ + R₃) (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L228-L246
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L228-L246

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

theorem QuarterSumLadder.coords_mod_eight :
    c0 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] ∧ c1 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] := by sorry
