-- Prove2me | Theorems.Thm_QuarterSumLadder_card_fiber
-- name    : QuarterSumLadder.card_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:05.407458+00:00
-- url     : https://prove2.me/theorems/9279a354-bac7-5cc5-a598-24515b190b87
-- title:
--   Quarter Sum Ladder: card fiber
-- statement:
--   Every class has `Q = (p - 1)/4` elements.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L141-L157
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L141-L157

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

theorem QuarterSumLadder.card_fiber {z : GaussianInt} (hz : FourVal z) : (fiber χ z).card = Q p := by sorry
