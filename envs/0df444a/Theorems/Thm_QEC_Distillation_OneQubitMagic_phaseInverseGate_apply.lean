-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseInverseGate_apply
-- name    : QEC.Distillation.OneQubitMagic.phaseInverseGate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:55:33.41393+00:00
-- url     : https://prove2.me/theorems/01f0cc38-d74b-4cd9-a426-555ec0704632
-- title:
--   One Qubit Magic: phase Inverse Gate apply
-- statement:
--   The inverse gate action is exactly the existing inverse phase operator action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L95-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L95-L98

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseInverseGate_apply (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseInverseGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseInverseOperator psi := by sorry
