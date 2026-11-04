-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_arena_ok
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.arena_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:24:14.769596+00:00
-- url     : https://prove2.me/theorems/b1549db1-7488-4cc1-b6fc-7617bb700fd2
-- title:
--   Weighted Global Colored Solver Need: arena ok
-- statement:
--   The Weighted Global Colored Solver Need construction uses the arena ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L160-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L160-L181

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

theorem ThreeSum.WeightedGlobalColoredSolverNeed.arena_ok {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d a bN c : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) (ha : a≤n) (hb : bN≤n) (hc : c≤n) :
    (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim
      (arenaFree free n (LightColorParametersCosts.width n) a bN c (LightWeightedGlobalDimensions.J M b n U) U) (d+100) := by sorry
