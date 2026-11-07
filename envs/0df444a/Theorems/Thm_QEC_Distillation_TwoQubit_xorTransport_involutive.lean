-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
-- name    : QEC.Distillation.TwoQubit.xorTransport_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:35.000272+00:00
-- url     : https://prove2.me/theorems/53b888ed-4a33-4d2f-8209-d5a4bb9e5420
-- title:
--   Two Qubit: xor Transport involutive
-- statement:
--   The Two Qubit construction uses the xor Transport involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L147-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L147-L165

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct

theorem QEC.Distillation.TwoQubit.xorTransport_involutive (psi : TwoQubitSpace) :
    xorTransport (xorTransport psi) = psi := by sorry
