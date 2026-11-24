-- Prove2me | Theorems.Thm_VickreyAward_foldr_min_le_mem
-- name    : VickreyAward.foldr_min_le_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:54.074025+00:00
-- url     : https://prove2.me/theorems/bc5951f3-3771-43b2-9798-fefc0363a159
-- title:
--   Vickrey Award: foldr min le mem
-- statement:
--   The Vickrey Award construction uses the foldr min le mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L59-L66
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/VickreyTruthful.lean#L59-L66

import Definitions.Def_VickreyTruthful
set_option autoImplicit true
open VickreyAward

theorem VickreyAward.foldr_min_le_mem (r : Nat) : ∀ (l : List Nat) (x : Nat), x ∈ l → l.foldr min r ≤ x
  := by sorry
