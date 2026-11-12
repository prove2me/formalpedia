-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_inverse
-- name    : QEC.Distillation.OneQubitMagic.phaseShiftGate_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:56:48.418062+00:00
-- url     : https://prove2.me/theorems/50a3982d-0b3a-4605-adc2-9fd2cf2e32b5
-- title:
--   One Qubit Magic: phase Shift Gate inverse
-- statement:
--   The One Qubit Magic construction uses the phase Shift Gate inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L185-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L185-L187

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseShiftGate_inverse (theta : Real) :
    (phaseShiftGate theta)⁻¹ = phaseShiftGate (-theta) := by sorry
