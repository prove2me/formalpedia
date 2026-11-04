-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_indexed_edge_iff
-- name    : ThreeSum.LocalMaskGraph.indexed_edge_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:41.593316+00:00
-- url     : https://prove2.me/theorems/eb71702c-f4eb-453b-854d-621736251eaa
-- title:
--   Local Mask Graph: indexed edge iff
-- statement:
--   The Local Mask Graph construction uses the indexed edge iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L86-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L86-L92

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators

theorem ThreeSum.LocalMaskGraph.indexed_edge_iff {L h i j : ℕ}
    (hi : i < vertexCount L h) (hj : j < vertexCount L h) :
    LightBooleanDot.dot (LightMaskBits.bit L (maskAt L h i))
      (LightMaskBits.bit L (maskAt L h j)) L = 0 ↔
      (setAt L h i,setAt L h j) ∈ LayerCounts.edgeSet L h := by sorry
