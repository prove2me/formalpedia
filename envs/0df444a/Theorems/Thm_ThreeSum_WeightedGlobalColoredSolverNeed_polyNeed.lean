-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_polyNeed
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:27:47.672482+00:00
-- url     : https://prove2.me/theorems/07c95656-b53d-41a9-a686-97c2ac9651ab
-- title:
--   Weighted Global Colored Solver Need: poly Need
-- statement:
--   The Weighted Global Colored Solver Need construction uses the poly Need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L99-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L99-L136

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedFrontendResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocationResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_polyNeed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalColoredSolverNeed.polyNeed {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (hM : 1<M) (hb : 1<b) :
    PolyNeed (need Alloc) := by sorry
