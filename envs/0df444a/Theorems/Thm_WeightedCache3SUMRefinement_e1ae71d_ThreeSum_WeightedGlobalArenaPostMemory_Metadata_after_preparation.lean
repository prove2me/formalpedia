-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPostMemory_Metadata_after_preparation
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory.Metadata.after_preparation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:36.805999+00:00
-- url     : https://prove2.me/theorems/d1821507-d5b9-4f6c-8ce6-769072b22050
-- title:
--   after_preparation
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L50-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L50-L67

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostMemory
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostMemory.Metadata.after_preparation {maps : Fin F→Weight m p} {τ : ℕ} {I : Input}
    {L q : ℕ} {μ ν : ℕ→ℤ} (M : Metadata (r := r) maps τ I μ)
    (hL : L+1≤I.capacity) (hq : q≤I.capacity)
    (hlo : addr I.free I.capacity 9≤I.prefixFree)
    (h : ∀x, LightTernaryFinalPreparation.Unwritten (addr I.free I.capacity 6) L
      (addr I.free I.capacity 7) (addr I.free I.capacity 8) q x→ν x=μ x) :
    Metadata (r := r) maps τ I ν := by sorry
