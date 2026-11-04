-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorReady_ready
-- name    : ThreeSum.WeightedGlobalArenaTensorReady.ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:14:24.132388+00:00
-- url     : https://prove2.me/theorems/a0cfdb1e-f2f8-49c6-8052-c374e5d503b7
-- title:
--   Weighted Global Arena Tensor Ready: ready
-- statement:
--   Literal arena layout and aggregate numeric guards suffice for every
--   four-coordinate source channel and the final paired polynomial circuit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorReady.lean#L33-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorReady.lean#L33-L136

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorReady
import Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
import Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_ready

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalTensorFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaTensorReady.ready {lim : Limits} {d J K U ls rs : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) (hF : 1<F) (hN : 0<N m r)
    (hw : (lim.space : ℤ)≤lim.word)
    (C : WeightedGlobalArenaCountReady.Capacity (lim := lim) (d := d+3) (r := r) maps τ cap I)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hprefix : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (hlocal : ∀right, 0<(localRecords maps cap right).length)
    (G : ∀right, WeightedGlobalArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space)
    (W : ∀right, WeightedGlobalArenaSourceControls.Controls (r := r) maps cap I right lim (d+3))
    (M : WeightedGlobalArenaSourceCountSeed.Reads (r := r) maps τ I μ)
    (header : Seg μ (addr I.free I.capacity 1) (setup (r := r) maps τ cap localQ I).argv)
    (leftEnd : ls+I.nB*(J+2)≤addr I.free I.capacity 23)
    (rightEnd : rs+I.nC*(J+2)≤addr I.free I.capacity 23)
    (hL : ∀i<I.nB,∀j<J+2, μ (ls+i*(J+2)+TernarySignedLayout.offset J j)=L i j)
    (hR : ∀i<I.nC,∀j<J+2, μ (rs+i*(J+2)+TernarySignedLayout.offset J j)=R i j)
    (bL : ∀i<I.nB,∀j<J+2, |L i j|≤(U : ℤ))
    (bR : ∀i<I.nC,∀j<J+2, |R i j|≤(U : ℤ))
    (hcap : U^2≤I.weightCap)
    (hheader : 106≤I.capacity)
    (htensor : (entries (r := r) maps τ I).length*(J+2)^4≤I.capacity)
    (hquad : 4≤I.capacity) (hpowers : 5≤I.capacity)
    (hcols : TernaryPairedColumnEnumeration.width K+1≤I.capacity)
    (hword : (WeightedGlobalTensorWordResources.word K J (entries (r := r) maps τ I).length
      (WeightedGlobalNativeMomentBounds.scoreBound (setup (r := r) maps τ cap localQ I)) U : ℤ)≤lim.word) :
    LightWeightedGlobalTensorFactory.Ready (setup (r := r) maps τ cap localQ I) lim d K J
      (addr I.free I.capacity 1) ls rs (addr I.free I.capacity 23)
      (addr I.free I.capacity 24) (addr I.free I.capacity 25)
      (addr I.free I.capacity 26) (addr I.free I.capacity 27)
      μ L R U (WeightedGlobalNativeMomentBounds.scoreBound (setup (r := r) maps τ cap localQ I)) := by sorry
