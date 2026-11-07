-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchDensity_toOperator
-- name    : QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:46.183684+00:00
-- url     : https://prove2.me/theorems/e1b4bef6-bd27-4e93-b226-5f2952262a43
-- title:
--   Two Qubit: zz Even Branch Density to Operator
-- statement:
--   The Two Qubit construction uses the zz Even Branch Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L113-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L113-L121

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics

theorem QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (zzEvenBranchDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzEvenBranchState psi h)
        (zzEvenBranchState psi h)).toLinearMap := by sorry
