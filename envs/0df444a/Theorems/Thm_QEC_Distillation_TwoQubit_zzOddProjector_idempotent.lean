-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_idempotent
-- name    : QEC.Distillation.TwoQubit.zzOddProjector_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:22:00.084742+00:00
-- url     : https://prove2.me/theorems/66ca41ea-2658-4c60-9c34-a01845bb0839
-- title:
--   Two Qubit: zz Odd Projector idempotent
-- statement:
--   The Two Qubit construction uses the zz Odd Projector idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L98-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L98-L102

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzOddProjector_idempotent :
    zzOddProjector * zzOddProjector = zzOddProjector := by sorry
