-- Prove2me | Theorems.Thm_VickreyAward_bid_le_price_of_wins
-- name    : VickreyAward.bid_le_price_of_wins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:25:18.963957+00:00
-- url     : https://prove2.me/theorems/138a573d-7ab4-4a0e-ad62-b61d4be0caee
-- title:
--   Vickrey Award: bid le price of wins
-- statement:
--   A winner is never paid less than its own bid (individual rationality at the true cost).
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L148-L150
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L148-L150

import Definitions.Def_VickreyTruthful
set_option autoImplicit true
open VickreyAward

theorem VickreyAward.bid_le_price_of_wins {r b : Nat} {before after : List Nat}
    (h : wins r before after b) : b ≤ price r before after := by sorry
