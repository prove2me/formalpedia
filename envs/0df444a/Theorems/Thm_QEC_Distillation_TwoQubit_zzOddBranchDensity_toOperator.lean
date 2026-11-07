-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchDensity_toOperator
-- name    : QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:08.183567+00:00
-- url     : https://prove2.me/theorems/228e22d3-4c1f-467d-a43c-810ddc96b7ed
-- title:
--   Two Qubit: zz Odd Branch Density to Operator
-- statement:
--   The Two Qubit construction uses the zz Odd Branch Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L123-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L123-L131

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics

theorem QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (zzOddBranchDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzOddBranchState psi h)
        (zzOddBranchState psi h)).toLinearMap := by sorry
