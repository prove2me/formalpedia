-- Prove2me | Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_mem
-- name    : ThreeSum.LocalMaskGraph.maskAt_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:50.097021+00:00
-- url     : https://prove2.me/theorems/3c92fe00-83e3-4314-af76-c6e65785620f
-- title:
--   Local Mask Graph: mask At mem
-- statement:
--   The Local Mask Graph construction uses the mask At mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L23-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean#L23-L28

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

theorem ThreeSum.LocalMaskGraph.maskAt_mem {L h i : ℕ} (hi : i < vertexCount L h) :
    maskAt L h i ∈ enumerateLayer L h := by sorry
