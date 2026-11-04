-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
-- name    : ThreeSum.WeightedGlobalArenaPhaseFrames.output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T01:07:24.352888+00:00
-- url     : https://prove2.me/theorems/8e311478-d58c-4a56-a956-35a72a518711
-- title:
--   Weighted Global Arena Phase Frames: output
-- statement:
--   Full concrete phase output preserves the templates and stored constants;
--   all frames are derived from the actual phase's component receipts.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseFrames.lean#L66-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseFrames.lean#L66-L121

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseFrames
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPhaseFrames
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open WeightedGlobalArenaControllerPlan WeightedGlobalArenaScoreScan
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSeedData WeightedGlobalArenaPrefixInputs WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation WeightedGlobalArenaPhase
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPhaseFrames.output {lim : Limits} {depth K H M b drift scale n U seedCount featureBound tagBound positionCap j U0 alpha beta budgetScale : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim I.free (depth+1))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hm : 0<m) (hr : j+1≤Nat.clog M (n^2)) (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hpos : positionCap≤n) (hseeds : seedCount≤(p^(LightWeightedGlobalDimensions.dim M b p K n U))^2)
    (hweight : I.weightCap≤WeightedGlobalArenaPrefixFootprints.weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) (hfamily : 1<F)
    (hlocal : ∀right,0<(localRecords maps cap right).length)
    (htime : WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=j+1) I (valueCap (r:=j+1) maps cap I)≤I.queryTime)
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (HM : WeightedGlobalArenaPrefixState.Memory I A (fun i t=>L i t.val) (fun i t=>R i t.val)
      (fun i t=>O i t.val) j s catalog initial μ)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (WeightedGlobalArenaHeaderAgreement.templateValues I p m F))
    (hSeed : Seg μ (addr I.free I.capacity 3)
      (LightWeightedGlobalPrefixFinish.header (config p j I A 0) seedCount (p^j) (p^j) (alpha^j)
        (9^j*n^2) (9^j*n^2) (U0*(beta*budgetScale)^j) (addr I.free I.capacity 8)))
    (hPrepare : WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j A.J n U0 alpha beta budgetScale I Q)≤I.capacity)
    (hτ : 0<τ) (hnonempty : 1≤(WeightedGlobalGoodOutputCatalog.raws maps τ).length)
    (hSelector : (LightTernaryRowSelector.word seedCount
      (WeightedGlobalArenaPrefixFootprints.numbers maps τ cap M b K H drift scale n U (j+1)).candidateScore
      (p^(j+1)) (p^(j+1)) (alpha^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (U0*(beta*budgetScale)^(j+1)):ℤ)≤lim.word)
    (hGood : ∃i<seedCount,LightTernaryRowSelector.Good
      (family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).flag
      (family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).scoreB
      (family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).scoreC
      ((family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).scoreP K)
      (p^(j+1)) (p^(j+1)) (alpha^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2) (U0*(beta*budgetScale)^(j+1)) i)
    (ω : ℕ→ℤ) (hω : (WeightedGlobalArenaPhase.phase (depth:=depth) (K:=K) (H:=H) (M:=M) (b:=b) (drift:=drift)
      (scale:=scale) (n:=n) (U:=U) (seedCount:=seedCount) (featureBound:=featureBound)
      (tagBound:=tagBound) (positionCap:=positionCap) (j:=j) (U0:=U0) (alpha:=alpha)
      (beta:=beta) (budgetScale:=budgetScale) maps τ cap Q Alloc I A ℓ seeds L R O s catalog
      initial μ hok hcap hm hr hJ hnB hnC hO hpos hseeds hweight htag hweightLower hprefix
      hfamily hlocal htime h HM hTemplate hSeed hPrepare hτ hnonempty hSelector hGood).Output ω) :
    ∀x,Stable I x→ω x=μ x := by sorry
