-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_injective
-- name    : ThreeSum.LocalMaskGraph.maskAt_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:07.271235+00:00
-- url     : https://prove2.me/theorems/655293ef-f27b-43ae-ab3c-a8f1e2479ca5
-- title:
--   Local Mask Graph: mask At injective
-- statement:
--   The Local Mask Graph construction uses the mask At injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L39-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L39-L43

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

theorem ThreeSum.LocalMaskGraph.maskAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : maskAt L h i = maskAt L h j) : i=j := by sorry
