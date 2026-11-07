-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_branchState
-- name    : QEC.Distillation.TwoQubit.zzEvenProjector_branchState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:04.611359+00:00
-- url     : https://prove2.me/theorems/66920709-161f-4f07-9bc1-0e251e937a9e
-- title:
--   Two Qubit: zz Even Projector branch State
-- statement:
--   The Two Qubit construction uses the zz Even Projector branch State property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L55-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/ParityBranches.lean#L55-L62

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics

theorem QEC.Distillation.TwoQubit.zzEvenProjector_branchState
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    zzEvenProjector (zzEvenBranchState psi h) =
      zzEvenBranchState psi h := by sorry
