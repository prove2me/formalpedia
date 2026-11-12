-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_mul_neg
-- name    : QEC.Distillation.OneQubitMagic.phaseShiftGate_mul_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:54:00.648001+00:00
-- url     : https://prove2.me/theorems/e1813ee1-2cc9-47ef-b082-c00028cd8d7e
-- title:
--   One Qubit Magic: phase Shift Gate mul neg
-- statement:
--   The One Qubit Magic construction uses the phase Shift Gate mul neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L180-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L180-L183

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseShiftGate_mul_neg (theta : Real) :
    phaseShiftGate theta * phaseShiftGate (-theta) = 1 := by sorry
