-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaMomentResources_resources
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaMomentResources.resources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:34:08.884454+00:00
-- url     : https://prove2.me/theorems/9bf0d33c-76a0-4e88-ac59-756d5a9f6edb
-- title:
--   resources
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L66-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L66-L135

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaMomentResources
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaMomentResources.resources {lim : Limits} {d originalB originalC M n U H : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (μ : ℕ→ℤ) (B C : ℕ→ℤ)
    (hM : 1<M) (hr : r≤Nat.clog M (n^2)) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hseed : ∀ k<2*H+1, ∀ j≤k,
      WeightedSourceCountExecutionFactory.Seed (setup (r := r) maps τ cap Q I) lim (d+2)
        (addr I.free I.capacity 28) μ
        (LightWeightedGlobalMomentChannelFactory.leftWeights k j B)
        (LightWeightedGlobalMomentChannelFactory.rightWeights k j C))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth)
    (hend : finish I.free I.capacity≤lim.space)
    (hnBl : I.nB≤I.capacity) (hnCl : I.nC≤I.capacity)
    (hcount : (2*H+1)*(entries (r := r) maps τ I).length≤I.capacity)
    (hrecords : 3*(entries (r := r) maps τ I).length≤I.capacity)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 25)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 25)
    (hBspace : originalB+I.nB≤addr I.free I.capacity 25)
    (hCspace : originalC+I.nC≤addr I.free I.capacity 25)
    (hB : ∀ i<I.nB, μ (originalB+i)=B i)
    (hC : ∀ i<I.nC, μ (originalC+i)=C i)
    (hBabs : ∀ i<I.nB, |B i|≤(U : ℤ)) (hCabs : ∀ i<I.nC, |C i|≤(U : ℤ))
    (hchannelWord : ((channelNeed maps cap M H n U).word : ℤ)≤lim.word)
    (hargs : ∀ z∈LightWeightedGlobalMomentChannelFactory.args (setup (r := r) maps τ cap Q I)
      originalB originalC (addr I.free I.capacity 25), |z|≤lim.word) :
    LightWeightedGlobalCertifiedMomentDriver.Resources (setup (r := r) maps τ cap Q I) lim d
      originalB originalC (addr I.free I.capacity 25) (2*H+1)
      (r*alphaRank m) (r*alphaRank m) U
      (WeightedGlobalMomentChannelResources.scoreBound (envelope maps cap M n) U (2*H)) μ B C := by sorry
