-- Prove2me | Theorems.Thm_VickreyAward_price_le_cost_of_not_wins
-- name    : VickreyAward.price_le_cost_of_not_wins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:57.197795+00:00
-- url     : https://prove2.me/theorems/6a10e1aa-bae4-4d5d-b562-4cab7b48e879
-- title:
--   Vickrey Award: price le cost of not wins
-- statement:
--   If the true cost would not win, the price does not exceed it.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L90-L113
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L90-L113

import Definitions.Def_VickreyTruthful
set_option autoImplicit true
open VickreyAward

theorem VickreyAward.price_le_cost_of_not_wins {r c : Nat} {before after : List Nat}
    (h : ¬ wins r before after c) : price r before after ≤ c := by sorry
