-- Prove2me | Theorems.Thm_VickreyAward_truthful_nonneg
-- name    : VickreyAward.truthful_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:25:17.950886+00:00
-- url     : https://prove2.me/theorems/7acc69f4-07d9-4d58-997f-829d9b06a2a6
-- title:
--   Vickrey Award: truthful nonneg
-- statement:
--   Truthful bidding never yields a negative payoff.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L153-L159
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L153-L159

import Definitions.Def_VickreyTruthful
set_option autoImplicit true
open VickreyAward

theorem VickreyAward.truthful_nonneg (r : Nat) (before after : List Nat) (c : Nat) :
    0 ≤ utility r before after c c := by sorry
