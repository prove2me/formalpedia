-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaTerminalReceipt_signed_keys_of_memory
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTerminalReceipt.signed_keys_of_memory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:03:08.454218+00:00
-- url     : https://prove2.me/theorems/b9abe8e9-7481-4697-b424-e8b1d545e44b
-- title:
--   signed_keys_of_memory
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L182-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L182-L201

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable {K : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaTerminalReceipt.signed_keys_of_memory (I : Input) (A : Inputs) (s : State (p := p) A)
    (r U radix : ℕ) (X B C : ℕ→ℤ) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (H : WeightedGlobalArenaPrefixState.Memory I A
      (fun i t=>left U radix A.J B i t.val) (fun i t=>right U radix A.J C i t.val)
      (fun i t=>requester U radix A.J X i t.val) r s catalog initial μ) :
    Reads μ (addr I.free I.capacity 4) I.nB
      (fun i=>TernaryExtensionEncoding.coefficientCode
        (WeightedGlobalNativeRequesterCoverage.sourceLeft (selectedHash A s r) U radix (B i))) ∧
    Reads μ (addr I.free I.capacity 5) I.nC
      (fun i=>TernaryExtensionEncoding.coefficientCode
        (WeightedGlobalNativeRequesterCoverage.sourceRight (selectedHash A s r) U radix (C i))) := by sorry
