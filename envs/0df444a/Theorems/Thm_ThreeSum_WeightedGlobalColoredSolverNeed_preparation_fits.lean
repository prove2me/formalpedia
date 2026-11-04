-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_preparation_fits
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.preparation_fits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:19:50.941708+00:00
-- url     : https://prove2.me/theorems/b1ea7ff5-c5f9-4dca-a27a-291d093bebe7
-- title:
--   Weighted Global Colored Solver Need: preparation fits
-- statement:
--   The Weighted Global Colored Solver Need construction uses the preparation fits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L150-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L150-L158

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

theorem ThreeSum.WeightedGlobalColoredSolverNeed.preparation_fits {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) :
    LightWeightedGlobalColorPreparationProof.space free n (LightWeightedGlobalDimensions.J M b n U) U≤lim.space := by sorry
