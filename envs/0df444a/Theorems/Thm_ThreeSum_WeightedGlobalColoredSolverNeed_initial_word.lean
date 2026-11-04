-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_initial_word
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.initial_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:21:10.930345+00:00
-- url     : https://prove2.me/theorems/f27d5da4-00bf-4060-a4fd-a7273a2aba96
-- title:
--   Weighted Global Colored Solver Need: initial word
-- statement:
--   The Weighted Global Colored Solver Need construction uses the initial word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L205-L220
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L205-L220

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

theorem ThreeSum.WeightedGlobalColoredSolverNeed.initial_word {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (n U nO : ℕ)
    (hnO : nO≤n*2^(LightWeightedGlobalDimensions.J M b n U)) :
    LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightWeightedGlobalDimensions.J M b n U) nO≤capacity Alloc.D Alloc.E (n+U) := by sorry
