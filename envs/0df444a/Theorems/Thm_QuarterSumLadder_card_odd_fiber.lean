-- Prove2me | Theorems.Thm_QuarterSumLadder_card_odd_fiber
-- name    : QuarterSumLadder.card_odd_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:12.936525+00:00
-- url     : https://prove2.me/theorems/b842a100-2aab-530f-9935-d6158aa9a771
-- title:
--   Quarter Sum Ladder: card odd fiber
-- statement:
--   Half of each class is odd.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L174-L178
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L174-L178

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

theorem QuarterSumLadder.card_odd_fiber {z : GaussianInt} (hz : FourVal z) :
    2 * ((fiber χ z).filter fun x => Odd x.val).card = Q p := by sorry
