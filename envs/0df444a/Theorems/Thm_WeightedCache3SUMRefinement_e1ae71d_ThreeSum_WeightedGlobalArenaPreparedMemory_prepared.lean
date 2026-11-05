-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPreparedMemory_prepared
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPreparedMemory.prepared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:11:52.541874+00:00
-- url     : https://prove2.me/theorems/1df75530-4236-4c17-a07a-4b6b93e78e6c
-- title:
--   prepared
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPreparedMemory.lean#L22-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPreparedMemory.lean#L22-L61

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixPreparedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixState_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.prepared


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPreparedMemory
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPreparedMemory.prepared (I : Input) (A : Inputs) (j n U0 a b scale : ℕ)
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
