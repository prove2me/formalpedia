-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInputs_prepared_ready
-- name    : ThreeSum.WeightedGlobalArenaPrefixInputs.prepared_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:57:09.509202+00:00
-- url     : https://prove2.me/theorems/696148ec-5492-4278-9961-c2d3b6fb25d5
-- title:
--   Weighted Global Arena Prefix Inputs: prepared ready
-- statement:
--   The genuine preparation execution discharges every bank/header/read premise
--   of controller readiness, including preservation of the old selected span.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInputs.lean#L137-L187
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInputs.lean#L137-L187

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedDataReads
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInputs
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixInputs
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation
open TernaryOriginalRowMenu WeightedGlobalNativeCompleteFrontend
open TernaryExtensionEncoding
open LightWeightedGlobalSeedScoreFactory
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixInputs.prepared_ready {lim : Limits} {depth K H M b drift scale n U seedCount featureBound tagBound positionCap j : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ ν : ℕ→ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : j+1≤Nat.clog M (n^2)) (hJ : A.J=LightWeightedGlobalDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hpos : positionCap≤n)
    (hseeds : seedCount≤(p^(LightWeightedGlobalDimensions.dim M b p K n U))^2)
    (hweight : I.weightCap≤WeightedGlobalArenaPrefixFootprints.weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hfamily : 1<F) (hN : 0<N m (j+1))
    (hlocal : ∀right,0<(localRecords maps cap right).length)
    (htime : WeightedGlobalArenaCountReady.queryTime (m := m) (r := j+1) I (valueCap (r := j+1) maps cap I)≤I.queryTime)
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (HM : WeightedGlobalArenaPrefixState.Memory I A (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) j s catalog initial μ)
    (U0 alpha beta budgetScale : ℕ)
    (HP : LightWeightedGlobalPrefixStep.Prepared
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j A.J n U0 alpha beta budgetScale I Q) μ ν)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (WeightedGlobalArenaHeaderAgreement.templateValues I p m F))
    (hτ : 0<τ) (hnonempty : 1≤(WeightedGlobalGoodOutputCatalog.raws maps τ).length) :
    WeightedGlobalArenaControllerCore.InputsReady (lim := lim) (depth := depth) (K := K)
      (U := tagBound) (n := seedCount) (positionCap := positionCap) maps τ cap Q I A
      (fun ordinal => data I A j featureBound ordinal ℓ (seeds ordinal) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) ν L R := by sorry
