-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleWord_det
-- name    : QEC.Distillation.OneQubitMagic.hAngleWord_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:19:34.551976+00:00
-- url     : https://prove2.me/theorems/8b42563d-e0d1-4dbb-828b-96753b8b4293
-- title:
--   One Qubit Magic: h Angle Word det
-- statement:
--   The explicit H-route word has determinant one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L164-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L164-L170

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.hAngleWord_det :
    (hAngleWord : SingleQubitMatrix).det = 1 := by sorry
