-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_preparation_space
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.preparation_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:20:33.643202+00:00
-- url     : https://prove2.me/theorems/e087a9c2-247c-49cb-8b6a-b09b34457835
-- title:
--   Weighted Global Colored Solver Need: preparation space
-- statement:
--   The Weighted Global Colored Solver Need construction uses the preparation space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L81-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L81-L83

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

theorem ThreeSum.WeightedGlobalColoredSolverNeed.preparation_space (M b n U : ℕ) :
    LightWeightedGlobalColorPreparationProof.space 0 n (LightWeightedGlobalDimensions.J M b n U) U≤
      preparationCells M b n U := by sorry
