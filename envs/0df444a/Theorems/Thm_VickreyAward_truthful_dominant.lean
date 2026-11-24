-- Prove2me | Theorems.Thm_VickreyAward_truthful_dominant
-- name    : VickreyAward.truthful_dominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:58.468767+00:00
-- url     : https://prove2.me/theorems/bf13e8e5-4439-4c52-ad64-2ba3d46f6bdd
-- title:
--   Vickrey Award: truthful dominant
-- statement:
--   **Truthful bidding is weakly dominant under `award.vickrey`.**
--       For every reserve, every profile of other bids (any number, any commit order),
--       every true cost `c` and every alternative bid `b`, bidding `c` pays at least as
--       much as bidding `b`.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L121-L131
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L121-L131

import Definitions.Def_VickreyTruthful
set_option autoImplicit true
open VickreyAward

theorem VickreyAward.truthful_dominant (r : Nat) (before after : List Nat) (c b : Nat) :
    utility r before after c b ≤ utility r before after c c := by sorry
