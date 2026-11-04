-- Prove2me | Theorems.Thm_ThreeSum_SubsetTransport_sum_powerset_map
-- name    : ThreeSum.SubsetTransport.sum_powerset_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:15.867832+00:00
-- url     : https://prove2.me/theorems/672bc279-9bb3-404b-bc55-cb23b0d85df8
-- title:
--   Subset Transport: sum powerset map
-- statement:
--   The Subset Transport construction uses the sum powerset map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L22-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L22-L28

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem ThreeSum.SubsetTransport.sum_powerset_map (e : α ≃ β) (S : Finset α) (f : Finset β → ℤ) :
    (∑ T ∈ (S.map e.toEmbedding).powerset, f T) =
      ∑ T ∈ S.powerset, f (T.map e.toEmbedding) := by sorry
