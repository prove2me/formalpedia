-- Prove2me | Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_succ
-- name    : ThreeSum.ExplicitLayers.valueSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:54.248868+00:00
-- url     : https://prove2.me/theorems/cc00059b-81b8-4976-bd04-4ec6a534511a
-- title:
--   Explicit Layers: value Sum succ
-- statement:
--   The Explicit Layers construction uses the value Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L33-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L33-L37

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers
set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ExplicitLayers.valueSum_succ {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    valueSum Q weight (t+1) = valueSum Q weight t+
      ((QueryCoordinates.missingSets Q t).map fun U => weight (Q \ U)).sum := by sorry
