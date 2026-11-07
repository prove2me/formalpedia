-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchState_rescale
-- name    : QEC.Distillation.TwoQubit.zzEvenBranchState_rescale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:58.009623+00:00
-- url     : https://prove2.me/theorems/23e39630-606f-4656-94c5-6012c3558a48
-- title:
--   Two Qubit: zz Even Branch State rescale
-- statement:
--   The Two Qubit construction uses the zz Even Branch State rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L73-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L73-L82

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics

theorem QEC.Distillation.TwoQubit.zzEvenBranchState_rescale
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (Real.sqrt (zzEvenWeight psi) : Complex) •
        zzEvenBranchState psi h =
      zzEvenProjector psi := by sorry
