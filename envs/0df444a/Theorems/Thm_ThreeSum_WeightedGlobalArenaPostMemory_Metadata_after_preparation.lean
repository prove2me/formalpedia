-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostMemory_Metadata_after_preparation
-- name    : ThreeSum.WeightedGlobalArenaPostMemory.Metadata.after_preparation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:46:47.198581+00:00
-- url     : https://prove2.me/theorems/534c20ba-ff2c-4644-886a-708388e715d4
-- title:
--   Metadata: after preparation
-- statement:
--   The Metadata construction uses the after preparation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L50-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L50-L67

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPostMemory
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPostMemory.Metadata.after_preparation {maps : Fin F→Weight m p} {τ : ℕ} {I : Input}
    {L q : ℕ} {μ ν : ℕ→ℤ} (M : Metadata (r := r) maps τ I μ)
    (hL : L+1≤I.capacity) (hq : q≤I.capacity)
    (hlo : addr I.free I.capacity 9≤I.prefixFree)
    (h : ∀x, LightTernaryFinalPreparation.Unwritten (addr I.free I.capacity 6) L
      (addr I.free I.capacity 7) (addr I.free I.capacity 8) q x→ν x=μ x) :
    Metadata (r := r) maps τ I ν := by sorry
