-- Prove2me | Theorems.Thm_ThreeSum_ExplicitLayers_sparse_identity
-- name    : ThreeSum.ExplicitLayers.sparse_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:01.739105+00:00
-- url     : https://prove2.me/theorems/d1b6887d-4c24-4b4c-8dd9-502e4e64554e
-- title:
--   Explicit Layers: sparse identity
-- statement:
--   The Explicit Layers construction uses the sparse identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L57-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L57-L61

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers
set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ExplicitLayers.sparse_identity {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    (∑ S ∈ Q.powerset, weight S) = valueSum Q weight t+
      ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight := by sorry
