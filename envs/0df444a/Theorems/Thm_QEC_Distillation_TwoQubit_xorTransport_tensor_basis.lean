-- Prove2me | Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
-- name    : QEC.Distillation.TwoQubit.xorTransport_tensor_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:20:43.798833+00:00
-- url     : https://prove2.me/theorems/19b28ba4-796c-4f27-b6cd-70f8950f9037
-- title:
--   Two Qubit: xor Transport tensor basis
-- statement:
--   The Two Qubit construction uses the xor Transport tensor basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L174-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean#L174-L186

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct

theorem QEC.Distillation.TwoQubit.xorTransport_tensor_basis (a b : Fin 2) :
    xorTransport
        (tensorRegisterTransport
          (EuclideanSpace.basisFun (Fin 2) Complex a ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex b)) =
      tensorRegisterTransport
        (EuclideanSpace.basisFun (Fin 2) Complex a ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex
            (controlledXBit a b)) := by sorry
