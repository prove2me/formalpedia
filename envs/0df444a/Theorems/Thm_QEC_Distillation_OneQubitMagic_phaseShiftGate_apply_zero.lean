-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_zero
-- name    : QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:47:00.194866+00:00
-- url     : https://prove2.me/theorems/0b2493e6-5e72-450c-be44-956f91d49050
-- title:
--   One Qubit Magic: phase Shift Gate apply zero
-- statement:
--   The One Qubit Magic construction uses the phase Shift Gate apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L129-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L129-L133

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_zero (theta : Real) (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi 0 =
      psi 0 := by sorry
