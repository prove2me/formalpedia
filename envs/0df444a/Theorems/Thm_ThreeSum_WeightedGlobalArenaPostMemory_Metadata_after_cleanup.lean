-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostMemory_Metadata_after_cleanup
-- name    : ThreeSum.WeightedGlobalArenaPostMemory.Metadata.after_cleanup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:47:41.277921+00:00
-- url     : https://prove2.me/theorems/e3905521-3122-4adf-b45c-16a9f2cc1283
-- title:
--   Metadata: after cleanup
-- statement:
--   The Metadata construction uses the after cleanup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L25-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L25-L48

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPostMemory
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPostMemory.Metadata.after_cleanup {maps : Fin F→Weight m p} {τ : ℕ} {I : Input}
    {aBase nA bBase nB cBase nC q L : ℕ} {keysB keysC : ℕ→ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (hB : nB≤I.capacity) (hC : nC≤I.capacity)
    (hcounts : nB+3*nC+1≤I.capacity) (hCc : nC+1≤I.capacity)
    (hlo : addr I.free I.capacity 11≤I.prefixFree)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 16)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (h : (WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase nB cBase nC q L).Unchanged keysB keysC μ ν) :
    Metadata (r := r) maps τ I ν := by sorry
