-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
-- name    : QEC.Distillation.TwoQubit.xorTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:27.369178+00:00
-- url     : https://prove2.me/theorems/705240df-3bd5-4014-9831-a347cc7b9ea7
-- title:
--   Two Qubit: xor Transport apply basis
-- statement:
--   The Two Qubit construction uses the xor Transport apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L138-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L138-L145

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct

theorem QEC.Distillation.TwoQubit.xorTransport_apply_basis (bits : Bitstring (Fin 2)) :
    xorTransport
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
        (xorBitstring bits) := by sorry
