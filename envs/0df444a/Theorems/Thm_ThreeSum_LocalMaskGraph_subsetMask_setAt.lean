-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_subsetMask_setAt
-- name    : ThreeSum.LocalMaskGraph.subsetMask_setAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:36:18.820696+00:00
-- url     : https://prove2.me/theorems/793d4c5e-c0bd-48e6-913f-32c3fac9d972
-- title:
--   Local Mask Graph: subset Mask set At
-- statement:
--   The Local Mask Graph construction uses the subset Mask set At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L36-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L36-L37

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

theorem ThreeSum.LocalMaskGraph.subsetMask_setAt {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := by sorry
