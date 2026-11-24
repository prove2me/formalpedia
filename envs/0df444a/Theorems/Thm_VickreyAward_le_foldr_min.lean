-- Prove2me | Theorems.Thm_VickreyAward_le_foldr_min
-- name    : VickreyAward.le_foldr_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:55.994586+00:00
-- url     : https://prove2.me/theorems/d76df53a-f300-480b-adbe-ead649550e8d
-- title:
--   Vickrey Award: le foldr min
-- statement:
--   The Vickrey Award construction uses the le foldr min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L68-L75
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L68-L75

import Definitions.Def_VickreyTruthful
set_option autoImplicit true
open VickreyAward

theorem VickreyAward.le_foldr_min (r c : Nat) (hr : c ≤ r) :
    ∀ l : List Nat, (∀ x ∈ l, c ≤ x) → c ≤ l.foldr min r
  := by sorry
