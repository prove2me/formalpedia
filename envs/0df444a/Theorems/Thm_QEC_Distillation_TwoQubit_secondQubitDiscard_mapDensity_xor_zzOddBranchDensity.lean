-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_secondQubitDiscard_mapDensity_xor_zzOddBranchDensity
-- name    : QEC.Distillation.TwoQubit.secondQubitDiscard_mapDensity_xor_zzOddBranchDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:10:44.834609+00:00
-- url     : https://prove2.me/theorems/cd995639-4f26-48c0-8447-469ffff3def4
-- title:
--   Two Qubit: second Qubit Discard map Density xor zz Odd Branch Density
-- statement:
--   The Two Qubit construction uses the second Qubit Discard map Density xor zz Odd Branch Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Discard.lean#L318-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Discard.lean#L318-L332

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

theorem QEC.Distillation.TwoQubit.secondQubitDiscard_mapDensity_xor_zzOddBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity
        (zzOddBranchDensity psi h) =
      zzOddBranchFirstDensity psi h := by sorry
