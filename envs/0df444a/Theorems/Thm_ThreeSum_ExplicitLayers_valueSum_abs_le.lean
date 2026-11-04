-- Prove2me | Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_abs_le
-- name    : ThreeSum.ExplicitLayers.valueSum_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:58.36168+00:00
-- url     : https://prove2.me/theorems/d1afe5e2-00a9-46f9-b8ef-3718f629dc2f
-- title:
--   Explicit Layers: value Sum abs le
-- statement:
--   The Explicit Layers construction uses the value Sum abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L39-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L39-L48

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers
set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ExplicitLayers.valueSum_abs_le {W B : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ)
    (hw : ∀ S, S ⊆ Q → |weight S| ≤ B) :
    |valueSum Q weight t| ≤ ((layerOffset Q.card t*B : ℕ) : ℤ) := by sorry
