-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply
-- name    : QEC.Distillation.OneQubitMagic.phaseGate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:48:20.886649+00:00
-- url     : https://prove2.me/theorems/91a414ae-ded6-4674-b08c-0dd1a9b87363
-- title:
--   One Qubit Magic: phase Gate apply
-- statement:
--   The gate action is exactly the existing Clifford phase transport action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L89-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L89-L92

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseGate_apply (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseTransport psi := by sorry
