-- Prove2me | Theorems.Thm_VickreyAward_wins_of_le
-- name    : VickreyAward.wins_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:59.056853+00:00
-- url     : https://prove2.me/theorems/09fe073e-6f77-4079-9860-16c978416c1b
-- title:
--   Vickrey Award: wins of le
-- statement:
--   Condition 5 (monotonicity): lowering a winning bid keeps it winning.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L136-L141
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L136-L141

import Definitions.Def_VickreyTruthful
set_option autoImplicit true
open VickreyAward

theorem VickreyAward.wins_of_le {r : Nat} {before after : List Nat} {b b' : Nat}
    (h : wins r before after b) (hle : b' ≤ b) : wins r before after b' := by sorry
