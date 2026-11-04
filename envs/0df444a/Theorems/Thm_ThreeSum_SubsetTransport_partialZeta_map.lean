-- Prove2me | Theorems.Thm_ThreeSum_SubsetTransport_partialZeta_map
-- name    : ThreeSum.SubsetTransport.partialZeta_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:01.803285+00:00
-- url     : https://prove2.me/theorems/275df6d0-93eb-4b75-a8c1-f7a23ff6f496
-- title:
--   Subset Transport: partial Zeta map
-- statement:
--   The Subset Transport construction uses the partial Zeta map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L42-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L42-L49

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem ThreeSum.SubsetTransport.partialZeta_map (e : α ≃ β) (f : Finset α → ℤ) (processed S : Finset α) :
    Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (S.map e.toEmbedding) =
      Subset.partialZeta processed f S := by sorry
