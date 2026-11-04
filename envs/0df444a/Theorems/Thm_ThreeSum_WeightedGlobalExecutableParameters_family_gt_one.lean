-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalExecutableParameters_family_gt_one
-- name    : ThreeSum.WeightedGlobalExecutableParameters.family_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:00:19.181577+00:00
-- url     : https://prove2.me/theorems/7ba347be-9b2a-44aa-8ced-f0686e1aed44
-- title:
--   Weighted Global Executable Parameters: family gt one
-- statement:
--   The Weighted Global Executable Parameters construction uses the family gt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutableParameters.lean#L23-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutableParameters.lean#L23-L31

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExecutableParameters
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverGoodMaps
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters WeightedGlobalNativeCoverWitness WeightedGlobalCoverScale
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalExecutableParameters.family_gt_one {K : ℕ} (hK : 0<K) (m k : ℕ) : 1<F K m k := by sorry
