-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_isSymmetricProjection
-- name    : QEC.Distillation.TwoQubit.zzOddProjector_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:22:57.615216+00:00
-- url     : https://prove2.me/theorems/41918261-d4bd-445c-98c2-bc02f810495b
-- title:
--   Two Qubit: zz Odd Projector is Symmetric Projection
-- statement:
--   The Two Qubit construction uses the zz Odd Projector is Symmetric Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L110-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L110-L114

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzOddProjector_isSymmetricProjection :
    zzOddProjector.IsSymmetricProjection := by sorry
