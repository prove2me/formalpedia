-- Prove2me | Theorems.Thm_QuarterSumLadder_card_half_fiber
-- name    : QuarterSumLadder.card_half_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:42.518945+00:00
-- url     : https://prove2.me/theorems/d89c8cca-01e1-5edb-8795-dc30ebcaf72f
-- title:
--   Quarter Sum Ladder: card half fiber
-- statement:
--   Half of each class lies in `(0, p/2)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L167-L171
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L167-L171

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.card_half_fiber {z : GaussianInt} (hz : FourVal z) :
    2 * ((fiber χ z).filter fun x => 2 * x.val < p).card = Q p := by sorry
