-- Prove2me | Theorems.Thm_ThreeSum_SubsetTransport_mobius_map
-- name    : ThreeSum.SubsetTransport.mobius_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:37.321089+00:00
-- url     : https://prove2.me/theorems/372a5a68-30d3-4f44-84a1-38e210fb515f
-- title:
--   Subset Transport: mobius map
-- statement:
--   The Subset Transport construction uses the mobius map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L36-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L36-L40

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem ThreeSum.SubsetTransport.mobius_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    Subset.mobius (reindex e f) (S.map e.toEmbedding) = Subset.mobius f S := by sorry
