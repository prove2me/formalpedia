-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_injective
-- name    : ThreeSum.LocalMaskGraph.setAt_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:51.962313+00:00
-- url     : https://prove2.me/theorems/81196f38-b3d6-4962-9891-0af318e383c7
-- title:
--   Local Mask Graph: set At injective
-- statement:
--   The Local Mask Graph construction uses the set At injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L45-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L45-L48

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

theorem ThreeSum.LocalMaskGraph.setAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : setAt L h i = setAt L h j) : i=j := by sorry
