-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPostResources_resources
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostResources.resources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:30.35957+00:00
-- url     : https://prove2.me/theorems/53b0738f-6892-438f-894a-0919ebf70624
-- title:
--   resources
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostResources.lean#L21-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostResources.lean#L21-L92

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostResources
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaMomentResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostResources.resources {lim : Limits} {d M n Hdet : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ ν : ℕ→ℤ)
    (hM : 1<M) (hr : r≤Nat.clog M (n^2)) (hF : 1<F) (hN : 0<N m r)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth)
    (hend : finish I.free I.capacity≤lim.space)
    (hcounts : I.nB+3*I.nC+1≤I.capacity) (hCc : I.nC+1≤I.capacity)
    (hlo : addr I.free I.capacity 11≤I.prefixFree)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 16)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (hrecords : 3*(entries (r := r) maps τ (selectedInput I U radix nA H A B C keysB keysC)).length≤I.capacity)
    (hcount : (2*Hdet+1)*(entries (r := r) maps τ (selectedInput I U radix nA H A B C keysB keysC)).length≤I.capacity)
    (hlocal : ∀right,0<(WeightedGlobalNativeCompleteFrontend.localRecords maps cap right).length)
    (G : ∀right,WeightedGlobalArenaSourceLayout.Geometry
      (source (r := r) maps cap (selectedInput I U radix nA H A B C keysB keysC) right) lim.space)
    (W : ∀right,WeightedGlobalArenaSourceControls.Controls (r := r) maps cap
      (selectedInput I U radix nA H A B C keysB keysC) right lim (d+3))
    (CC : WeightedGlobalArenaCountReady.Capacity (lim := lim) (d := d+3) (r := r) maps τ cap
      (selectedInput I U radix nA H A B C keysB keysC))
    (hweight : WeightedGlobalMomentWeightBounds.leftBound U (2*Hdet)≤I.weightCap)
    (hchannel : ((WeightedGlobalArenaMomentResources.channelNeed maps cap M Hdet n U).word : ℤ)≤lim.word)
    (hargs : ∀z∈LightWeightedGlobalMomentChannelFactory.args
      (setup (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC))
      (addr I.free I.capacity 10) (addr I.free I.capacity 16+I.nB+1+2*I.nC)
      (addr I.free I.capacity 25), |z|≤lim.word)
    (hB : ∀j<I.nB,|B j|≤(U : ℤ)) (hC : ∀j<I.nC,|C j|≤(U : ℤ))
    (Meta : WeightedGlobalArenaPostMemory.Metadata (r := r) maps τ
      (selectedInput I U radix nA H A B C keysB keysC) μ)
    (h : (WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L).Unchanged keysB keysC μ ν)
    (hOutB : Output ν keysB B I.nB (addr I.free I.capacity 9) (addr I.free I.capacity 10)
      (addr I.free I.capacity 16) (addr I.free I.capacity 16+I.nB))
    (hOutC : Output ν keysC C I.nC (addr I.free I.capacity 16+I.nB+1)
      (addr I.free I.capacity 16+I.nB+1+2*I.nC)
      (addr I.free I.capacity 17) (addr I.free I.capacity 17+I.nC))
    (hkB : ∀j<I.nB,keysB j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceLeft H U radix (B j)))
    (hkC : ∀j<I.nC,keysC j=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceRight H U radix (C j))) :
    LightWeightedGlobalCertifiedMomentDriver.Resources
      (setup (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)) lim d
      (addr I.free I.capacity 10) (addr I.free I.capacity 16+I.nB+1+2*I.nC)
      (addr I.free I.capacity 25) (2*Hdet+1)
      (r*alphaRank m) (r*alphaRank m) U
      (WeightedGlobalMomentChannelResources.scoreBound (WeightedGlobalArenaPairMass.envelope maps cap M n) U (2*Hdet))
      ν (compact keysB B I.nB) (compact keysC C I.nC) := by sorry
