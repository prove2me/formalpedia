-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
-- name    : QEC.Distillation.TwoQubit.xorTransport_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:50.776596+00:00
-- url     : https://prove2.me/theorems/d9ee1eb7-6f84-41f6-ae75-4b6a114f9e89
-- title:
--   Two Qubit: xor Transport symm apply
-- statement:
--   The Two Qubit construction uses the xor Transport symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L167-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L167-L172

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct

theorem QEC.Distillation.TwoQubit.xorTransport_symm_apply (psi : TwoQubitSpace) :
    xorTransport.symm psi = xorTransport psi := by sorry
