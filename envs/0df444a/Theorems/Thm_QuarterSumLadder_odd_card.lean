-- Prove2me | Theorems.Thm_QuarterSumLadder_odd_card
-- name    : QuarterSumLadder.odd_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:09.184798+00:00
-- url     : https://prove2.me/theorems/3033ab21-bf47-4de8-a857-590858afe75d
-- title:
--   Quarter Sum Ladder: odd card
-- statement:
--   The odd elements of a class have the same number, `Q/2`, in every class.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L129-L134
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L129-L134

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

theorem QuarterSumLadder.odd_card {z : GaussianInt} (hz : FourVal z) :
    2 * ((fiber χ z).filter fun x => x.val % 2 = 1).card = Q p := by sorry
