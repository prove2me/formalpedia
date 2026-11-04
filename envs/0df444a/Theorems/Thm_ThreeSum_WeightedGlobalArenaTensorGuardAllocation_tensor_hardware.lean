-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorGuardAllocation_tensor_hardware
-- name    : ThreeSum.WeightedGlobalArenaTensorGuardAllocation.tensor_hardware
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:19:00.515996+00:00
-- url     : https://prove2.me/theorems/5bda5147-c98a-485d-8bda-8a06a16c996c
-- title:
--   Weighted Global Arena Tensor Guard Allocation: tensor hardware
-- statement:
--   Numeric hardware form usable at nested controller depths inside the fixed reserve.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorGuardAllocation.lean#L152-L243
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorGuardAllocation.lean#L152-L243

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorGuardAllocation
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaTensorGuardAllocation.tensor_hardware {lim : Limits} {depth K H M b drift scale n U seed tagBound : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed)) (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (hend : finish I.free I.capacity≤lim.space)
    (hword : (I.capacity : ℤ)≤lim.word)
    (hdepth : depth+4+I.capacity≤lim.depth) (hw : (lim.space : ℤ)≤lim.word)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2)) (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hfamily : 1<F) (hN : 0<N m r)
    (hlocal : ∀right, 0<(localRecords maps cap right).length)
    (htime : WeightedGlobalArenaCountReady.queryTime (m := m) (r := r) I (valueCap (r := r) maps cap I)≤I.queryTime)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r))
    (ret : ℤ)
    (hheader : Seg μ (addr I.free I.capacity 1)
      (WeightedGlobalArenaHeaderAgreement.emittedHeader I p m F (r-1) Q ret))
    (leftEnd : A.leftTagged+I.nB*(A.J+2)≤addr I.free I.capacity 1)
    (rightEnd : A.rightTagged+I.nC*(A.J+2)≤addr I.free I.capacity 1)
    (leftRead : ∀i<I.nB,∀j<A.J+2, μ (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=L i j)
    (rightRead : ∀i<I.nC,∀j<A.J+2, μ (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=R i j)
    (leftBound : ∀i<I.nB,∀j<A.J+2, |L i j|≤(tagBound : ℤ))
    (rightBound : ∀i<I.nC,∀j<A.J+2, |R i j|≤(tagBound : ℤ)) :
    WeightedGlobalArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := tagBound)
      maps τ cap Q I A D μ L R := by sorry
