-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPreparedMemory_prepared
-- name    : ThreeSum.WeightedGlobalArenaPreparedMemory.prepared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:04:12.996197+00:00
-- url     : https://prove2.me/theorems/d9d0f873-71d1-4d4b-a457-2f9faae23dc1
-- title:
--   Weighted Global Arena Prepared Memory: prepared
-- statement:
--   The actual preparation receipt gives the next bank, powers, emitted
--   host header and retained old keys/span at the same final physical memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPreparedMemory.lean#L22-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPreparedMemory.lean#L22-L61

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_prepared
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPreparedMemory
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPreparedMemory.prepared (I : Input) (A : Inputs) (j n U0 a b scale : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ ν : ℕ→ℤ)
    (H : LightWeightedGlobalPrefixStep.Prepared
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j A.J n U0 a b scale I Q) μ ν)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hcap : 106≤I.capacity) (hB : I.nB≤I.capacity) (hC : I.nC≤I.capacity)
    (hO : I.requesterCount≤I.capacity) (hSpan : A.J*p^j≤I.capacity)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (WeightedGlobalArenaHeaderAgreement.templateValues I p m F))
    (HM : WeightedGlobalArenaPrefixState.Memory I A L R O j s catalog initial μ) :
    WeightedGlobalArenaPrefixState.Memory I A L R O j s catalog initial ν ∧
    Seg ν I.prefixFree ((bankCodes m (j+1)).map (fun (c : ℕ) => (c : ℤ))) ∧
    LightSubsetAddress.Powers ν (I.prefixFree+4^(N m (j+1))) (2*N m (j+1)) ∧
    ∃ret, Seg ν (addr I.free I.capacity 1)
      (WeightedGlobalArenaHeaderAgreement.emittedHeader I p m F j Q ret) := by sorry
