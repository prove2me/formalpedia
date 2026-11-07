-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchState_rescale
-- name    : QEC.Distillation.TwoQubit.zzOddBranchState_rescale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:41.535117+00:00
-- url     : https://prove2.me/theorems/a7d526ee-d6b5-48be-8942-6c4d4da881d0
-- title:
--   Two Qubit: zz Odd Branch State rescale
-- statement:
--   The Two Qubit construction uses the zz Odd Branch State rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L84-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L84-L93

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics

theorem QEC.Distillation.TwoQubit.zzOddBranchState_rescale
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (Real.sqrt (zzOddWeight psi) : Complex) •
        zzOddBranchState psi h =
      zzOddProjector psi := by sorry
