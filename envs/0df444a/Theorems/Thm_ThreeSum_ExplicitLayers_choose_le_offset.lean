-- Prove2me | Theorems.Thm_ThreeSum_ExplicitLayers_choose_le_offset
-- name    : ThreeSum.ExplicitLayers.choose_le_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:59.841229+00:00
-- url     : https://prove2.me/theorems/58de3b58-66d9-4e62-965c-f72cebc7e4e9
-- title:
--   Explicit Layers: choose le offset
-- statement:
--   The Explicit Layers construction uses the choose le offset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L23-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L23-L24

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers
set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ExplicitLayers.choose_le_offset {c j t : ℕ} (hj : j < t) : c.choose j ≤ layerOffset c t := by sorry
