-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorDriver_channelLibraries_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.channelLibraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:44:26.224211+00:00
-- url     : https://prove2.me/theorems/c0eef865-6453-4104-960c-cfbbe03ee552
-- title:
--   channelLibraries_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L30-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L30-L32

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryQuarticStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriver
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver
open Light

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorDriver.channelLibraries_length (xl yl zl xr yr zr : List ℤ) :
    (channelLibraries xl yl zl xr yr zr).length=138 := by sorry
