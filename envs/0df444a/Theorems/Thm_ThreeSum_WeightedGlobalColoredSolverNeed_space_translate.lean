-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_space_translate
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.space_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:21:47.045789+00:00
-- url     : https://prove2.me/theorems/240ee2db-5485-41a9-86fc-77960fa121d0
-- title:
--   Weighted Global Colored Solver Need: space translate
-- statement:
--   The Weighted Global Colored Solver Need construction uses the space translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L33-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L33-L37

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalColoredSolverNeed.space_translate (free n J U : ℕ) :
    LightWeightedGlobalColorPreparationProof.space free n J U=
      free+LightWeightedGlobalColorPreparationProof.space 0 n J U := by sorry
