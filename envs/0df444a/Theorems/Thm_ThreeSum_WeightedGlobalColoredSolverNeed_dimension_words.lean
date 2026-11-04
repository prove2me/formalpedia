-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredSolverNeed_dimension_words
-- name    : ThreeSum.WeightedGlobalColoredSolverNeed.dimension_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:21:06.292017+00:00
-- url     : https://prove2.me/theorems/3abc80a4-4cb3-4fb5-9047-dbf38944061a
-- title:
--   Weighted Global Colored Solver Need: dimension words
-- statement:
--   The Weighted Global Colored Solver Need construction uses the dimension words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L183-L196
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L183-L196

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

theorem ThreeSum.WeightedGlobalColoredSolverNeed.dimension_words {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) :
    (LightWeightedGlobalDimensions.r M n:ℤ)≤lim.word ∧
    (LightWeightedGlobalDimensions.J M b n U:ℤ)≤lim.word ∧
    (LightWeightedGlobalDimensions.dim M b p K n U:ℤ)≤lim.word ∧
    ((p^(LightWeightedGlobalDimensions.dim M b p K n U):ℕ):ℤ)≤lim.word := by sorry
