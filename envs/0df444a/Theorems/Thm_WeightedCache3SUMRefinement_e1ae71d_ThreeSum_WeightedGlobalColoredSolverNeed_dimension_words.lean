-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredSolverNeed_dimension_words
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSolverNeed.dimension_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:50:54.196661+00:00
-- url     : https://prove2.me/theorems/2ec418fe-ad81-4ff9-aa58-9b6415984675
-- title:
--   dimension_words
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L183-L196
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredSolverNeed.lean#L183-L196

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSolverNeed
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredSolverNeed.dimension_words {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) :
    (LightWeightedGlobalDimensions.r M n:ℤ)≤lim.word ∧
    (LightWeightedGlobalDimensions.J M b n U:ℤ)≤lim.word ∧
    (LightWeightedGlobalDimensions.dim M b p K n U:ℤ)≤lim.word ∧
    ((p^(LightWeightedGlobalDimensions.dim M b p K n U):ℕ):ℤ)≤lim.word := by sorry
