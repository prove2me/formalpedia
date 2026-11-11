-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply
-- name    : QEC.Distillation.OneQubitMagic.phaseShiftGate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:48:39.456458+00:00
-- url     : https://prove2.me/theorems/025cc11c-f5e6-4943-be3e-fba40d20c98e
-- title:
--   One Qubit Magic: phase Shift Gate apply
-- statement:
--   The gate action is exactly the existing diagonal phase transport action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L101-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L101-L104

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseShiftGate_apply (theta : Real) (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseShiftTransport theta psi := by sorry
