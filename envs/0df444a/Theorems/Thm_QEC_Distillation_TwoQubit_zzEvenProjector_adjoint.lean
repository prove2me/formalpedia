-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_adjoint
-- name    : QEC.Distillation.TwoQubit.zzEvenProjector_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:21:58.743911+00:00
-- url     : https://prove2.me/theorems/acbcf90a-bbab-4dd3-9786-275218e29dee
-- title:
--   Two Qubit: zz Even Projector adjoint
-- statement:
--   The Two Qubit construction uses the zz Even Projector adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L70-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L70-L79

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzEvenProjector_adjoint :
    LinearMap.adjoint zzEvenProjector = zzEvenProjector := by sorry
