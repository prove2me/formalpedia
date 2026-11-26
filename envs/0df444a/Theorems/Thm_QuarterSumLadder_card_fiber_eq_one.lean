-- Prove2me | Theorems.Thm_QuarterSumLadder_card_fiber_eq_one
-- name    : QuarterSumLadder.card_fiber_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:11.648024+00:00
-- url     : https://prove2.me/theorems/22de0ee8-0b92-4372-8e8d-c445a0155903
-- title:
--   Quarter Sum Ladder: card fiber eq one
-- statement:
--   The Quarter Sum Ladder construction uses the card fiber eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L128-L138
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L128-L138

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
omit hp8

theorem QuarterSumLadder.card_fiber_eq_one {z : GaussianInt} (hz : FourVal z) :
    (fiber χ z).card = (fiber χ 1).card := by sorry
