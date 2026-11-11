-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_one
-- name    : QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:46:58.492205+00:00
-- url     : https://prove2.me/theorems/652e87eb-ebc4-4e8d-a17f-8dc0f79ac119
-- title:
--   One Qubit Magic: phase Shift Gate apply one
-- statement:
--   The One Qubit Magic construction uses the phase Shift Gate apply one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L135-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L135-L139

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_one (theta : Real) (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi 1 =
      phaseAmplitude theta * psi 1 := by sorry
