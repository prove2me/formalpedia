-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity
-- name    : QEC.Distillation.TwoQubit.secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:09:53.554563+00:00
-- url     : https://prove2.me/theorems/cc3f536c-3907-475e-83ed-e0045439d446
-- title:
--   Two Qubit: second Qubit Discard map Density xor zz Even Branch Density
-- statement:
--   The Two Qubit construction uses the second Qubit Discard map Density xor zz Even Branch Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Discard.lean#L302-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Discard.lean#L302-L316

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Discard
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped InnerProductSpace TensorProduct

theorem QEC.Distillation.TwoQubit.secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity
        (zzEvenBranchDensity psi h) =
      zzEvenBranchFirstDensity psi h := by sorry
