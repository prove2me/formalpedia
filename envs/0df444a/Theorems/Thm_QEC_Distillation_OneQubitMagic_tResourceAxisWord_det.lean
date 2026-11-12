-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisWord_det
-- name    : QEC.Distillation.OneQubitMagic.tResourceAxisWord_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:19:25.405247+00:00
-- url     : https://prove2.me/theorems/2332ae57-bc7e-455d-bc62-6aba819e288e
-- title:
--   One Qubit Magic: t Resource Axis Word det
-- statement:
--   The explicit word has determinant one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L151-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L151-L157

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.tResourceAxisWord_det :
    (tResourceAxisWord : SingleQubitMatrix).det = 1 := by sorry
