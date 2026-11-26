-- Prove2me | Theorems.Thm_QuarterSumLadder_card_even_half
-- name    : QuarterSumLadder.card_even_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:28.20227+00:00
-- url     : https://prove2.me/theorems/79afd512-1716-4bca-bd54-f142f68b0596
-- title:
--   Quarter Sum Ladder: card even half
-- statement:
--   The even elements of a class in `(0, p/2)` are the doubles of the class of `χ(2) z` in
--   `(0, p/4)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L206-L233
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L206-L233

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

theorem QuarterSumLadder.card_even_half (z : GaussianInt) :
    ((fiber χ z).filter fun x => 2 * x.val < p ∧ Even x.val).card =
      ((fiber χ (χ 2 * z)).filter fun x => 4 * x.val < p).card := by sorry
