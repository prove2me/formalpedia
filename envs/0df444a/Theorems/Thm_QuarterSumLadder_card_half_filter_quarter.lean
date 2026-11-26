-- Prove2me | Theorems.Thm_QuarterSumLadder_card_half_filter_quarter
-- name    : QuarterSumLadder.card_half_filter_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:05.804804+00:00
-- url     : https://prove2.me/theorems/292c02ff-35b7-57fc-aeb0-e8820d84fe51
-- title:
--   Quarter Sum Ladder: card half filter quarter
-- statement:
--   The half part of a class, with `R_r` of its elements in `(0, p/4)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L91-L96
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L91-L96

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
omit hp8 hχ

theorem QuarterSumLadder.card_half_filter_quarter (z : GaussianInt) :
    (((fiber χ z).filter fun x => 2 * x.val < p).filter fun x => 4 * x.val < p) =
      (fiber χ z).filter fun x => 4 * x.val < p := by sorry
