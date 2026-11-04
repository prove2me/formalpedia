-- Prove2me | Theorems.Thm_ThreeSum_SubsetTransport_reindex_map
-- name    : ThreeSum.SubsetTransport.reindex_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:51:45.657525+00:00
-- url     : https://prove2.me/theorems/ca57dc7c-66c6-4da8-b31a-2ecfd7f8947b
-- title:
--   Subset Transport: reindex map
-- statement:
--   The Subset Transport construction uses the reindex map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L15-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L15-L20

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem ThreeSum.SubsetTransport.reindex_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    reindex e f (S.map e.toEmbedding) = f S := by sorry
