-- Prove2me | Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
-- name    : ThreeSum.ExplicitLayers.leaves_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:03.120928+00:00
-- url     : https://prove2.me/theorems/6ef3c65c-5eda-4bc3-a7c9-5f7f2579c749
-- title:
--   Explicit Layers: leaves length
-- statement:
--   The Explicit Layers construction uses the leaves length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L19-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L19-L21

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers
set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ExplicitLayers.leaves_length {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (SignedLeaf.explicitLeaves Q t).length = layerOffset Q.card t := by sorry
