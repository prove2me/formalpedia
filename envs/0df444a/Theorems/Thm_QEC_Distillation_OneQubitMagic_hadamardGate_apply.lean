-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply
-- name    : QEC.Distillation.OneQubitMagic.hadamardGate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:48:09.983311+00:00
-- url     : https://prove2.me/theorems/b9eae3d0-4e81-4128-a987-8c47423ae6e7
-- title:
--   One Qubit Magic: hadamard Gate apply
-- statement:
--   The gate action is exactly the existing Hadamard transport action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L83-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L83-L86

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.hadamardGate_apply (psi : QubitSpace) :
    Matrix.toEuclideanLin (hadamardGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      hadamardTransport psi := by sorry
