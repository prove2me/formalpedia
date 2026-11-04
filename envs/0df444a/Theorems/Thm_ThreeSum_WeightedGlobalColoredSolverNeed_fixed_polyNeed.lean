-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_fixed_polyNeed
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.fixed_polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:22:18.98708+00:00
-- url     : https://prove2.me/theorems/17a9d62e-5c6c-418e-bfb5-a06032e47bf1
-- title:
--   Weighted Global Colored Solver Need: fixed poly Need
-- statement:
--   The Weighted Global Colored Solver Need construction uses the fixed poly Need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L245-L247
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L245-L247

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

theorem ThreeSum.WeightedGlobalColoredSolverNeed.fixed_polyNeed {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (hM : 1<M) (hb : 1<b) (κ : ℕ) :
    PolyNeed (fixedNeed Alloc κ) := by sorry
