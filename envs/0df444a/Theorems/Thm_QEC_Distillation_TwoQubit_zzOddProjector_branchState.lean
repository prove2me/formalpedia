-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_branchState
-- name    : QEC.Distillation.TwoQubit.zzOddProjector_branchState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:09.119907+00:00
-- url     : https://prove2.me/theorems/daa9046a-3665-470f-b0e0-663dce64a93c
-- title:
--   Two Qubit: zz Odd Projector branch State
-- statement:
--   The Two Qubit construction uses the zz Odd Projector branch State property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L64-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L64-L71

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics

theorem QEC.Distillation.TwoQubit.zzOddProjector_branchState
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    zzOddProjector (zzOddBranchState psi h) =
      zzOddBranchState psi h := by sorry
