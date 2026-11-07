-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
-- name    : QEC.Distillation.TwoQubit.zzOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:21:40.391324+00:00
-- url     : https://prove2.me/theorems/9e3a5a0f-3a28-4f24-84e4-fbc470d73e69
-- title:
--   Two Qubit: zz Operator apply
-- statement:
--   The Two Qubit construction uses the zz Operator apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L20-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Parity.lean#L20-L24

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit

theorem QEC.Distillation.TwoQubit.zzOperator_apply (psi : TwoQubitSpace)
    (bits : Bitstring (Fin 2)) :
    zzOperator psi bits =
      zPhase (bits 0) * zPhase (bits 1) * psi bits := by sorry
