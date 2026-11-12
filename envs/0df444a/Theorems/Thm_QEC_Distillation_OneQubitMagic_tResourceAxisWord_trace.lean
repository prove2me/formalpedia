-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisWord_trace
-- name    : QEC.Distillation.OneQubitMagic.tResourceAxisWord_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:19:37.631257+00:00
-- url     : https://prove2.me/theorems/89a08e81-f3de-442b-86ce-ecb9dfdee450
-- title:
--   One Qubit Magic: t Resource Axis Word trace
-- statement:
--   The explicit word has the rational trace used in the Niven argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L160-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L160-L164

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.tResourceAxisWord_trace :
    Matrix.trace (tResourceAxisWord : SingleQubitMatrix) = 3 / 2 := by sorry
