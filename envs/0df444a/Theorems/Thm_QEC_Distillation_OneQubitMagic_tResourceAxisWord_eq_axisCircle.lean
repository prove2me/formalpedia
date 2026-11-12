-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisWord_eq_axisCircle
-- name    : QEC.Distillation.OneQubitMagic.tResourceAxisWord_eq_axisCircle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:06:23.850526+00:00
-- url     : https://prove2.me/theorems/7e7120a1-0793-4d20-855b-90ee803231f9
-- title:
--   One Qubit Magic: t Resource Axis Word eq axis Circle
-- statement:
--   The concrete word is literally the selected special-unitary axis-circle point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L137-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L137-L148

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.tResourceAxisWord_eq_axisCircle :
    tResourceAxisWord =
      axisCircle tResourceAxis
        (tResourceAxisAngle : AddCircle (2 * Real.pi)) := by sorry
