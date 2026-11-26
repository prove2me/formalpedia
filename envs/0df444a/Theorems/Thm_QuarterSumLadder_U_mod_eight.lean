-- Prove2me | Theorems.Thm_QuarterSumLadder_U_mod_eight
-- name    : QuarterSumLadder.U_mod_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:08:39.671805+00:00
-- url     : https://prove2.me/theorems/46d4ff38-de9b-5b30-80dd-8ef82fd125ea
-- title:
--   Quarter Sum Ladder: U mod eight
-- statement:
--   `U_z ≡ #(odd in D_z) + 4 E_z (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L138-L143
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L138-L143

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
omit hp8 hχ

theorem QuarterSumLadder.U_mod_eight (z : GaussianInt) :
    ((U χ z : ℤ) : ZMod 8) =
      (((fiber χ z).filter fun x => x.val % 2 = 1).card : ZMod 8) + 4 * (E χ z : ZMod 8) := by sorry
