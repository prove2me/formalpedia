-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostMemory_reads
-- name    : ThreeSum.WeightedGlobalArenaPostMemory.reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:48:33.523747+00:00
-- url     : https://prove2.me/theorems/a96e9d2e-d188-4c03-9ec3-9361cee600f4
-- title:
--   Weighted Global Arena Post Memory: reads
-- statement:
--   The Weighted Global Arena Post Memory construction uses the reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L77-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L77-L109

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

theorem ThreeSum.WeightedGlobalArenaPostMemory.reads {maps : Fin F→Weight m p} {τ cap : ℕ}
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ ν : ℕ→ℤ)
    (M : Metadata (r := r) maps τ (selectedInput I U radix nA H A B C keysB keysC) μ)
    (hcounts : I.nB+3*I.nC+1≤I.capacity) (hCc : I.nC+1≤I.capacity)
    (hlo : addr I.free I.capacity 11≤I.prefixFree)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 16)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (h : (WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L).Unchanged keysB keysC μ ν)
    (hOutB : Output ν keysB B I.nB (addr I.free I.capacity 9) (addr I.free I.capacity 10)
      (addr I.free I.capacity 16) (addr I.free I.capacity 16+I.nB))
    (hOutC : Output ν keysC C I.nC (addr I.free I.capacity 16+I.nB+1)
      (addr I.free I.capacity 16+I.nB+1+2*I.nC)
      (addr I.free I.capacity 17) (addr I.free I.capacity 17+I.nC))
    (hkB : ∀j<I.nB,keysB j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceLeft H U radix (B j)))
    (hkC : ∀j<I.nC,keysC j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceRight H U radix (C j))) :
    WeightedGlobalArenaSourceCountSeed.Reads (r := r) maps τ (selectedInput I U radix nA H A B C keysB keysC) ν := by sorry
