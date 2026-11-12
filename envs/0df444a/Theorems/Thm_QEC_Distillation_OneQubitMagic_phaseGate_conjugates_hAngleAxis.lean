-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_conjugates_hAngleAxis
-- name    : QEC.Distillation.OneQubitMagic.phaseGate_conjugates_hAngleAxis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:10:21.529358+00:00
-- url     : https://prove2.me/theorems/d45520b6-e0d9-4fb0-a4a7-ffbbe1b16fbc
-- title:
--   One Qubit Magic: phase Gate conjugates h Angle Axis
-- statement:
--   The phase Clifford transports the concrete H-route Pauli axis as stated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L215-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L215-L228

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseGate_conjugates_hAngleAxis :
    (phaseGate : SingleQubitMatrix) * axisPauliMatrix hAngleAxis *
        ((phaseGate⁻¹ : SingleQubitGate) : SingleQubitMatrix) =
      axisPauliMatrix hAngleConjugateAxis := by sorry
