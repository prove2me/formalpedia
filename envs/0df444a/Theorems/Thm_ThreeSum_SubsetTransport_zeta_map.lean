-- Prove2me | Theorems.Thm_ThreeSum_SubsetTransport_zeta_map
-- name    : ThreeSum.SubsetTransport.zeta_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:34.926367+00:00
-- url     : https://prove2.me/theorems/e2b2b660-1891-44d9-861d-60bdc8bf52ef
-- title:
--   Subset Transport: zeta map
-- statement:
--   The Subset Transport construction uses the zeta map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L30-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetTransport.lean#L30-L34

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetTransport
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetTransport
open Finset
open scoped BigOperators
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem ThreeSum.SubsetTransport.zeta_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    Subset.zeta (reindex e f) (S.map e.toEmbedding) = Subset.zeta f S := by sorry
