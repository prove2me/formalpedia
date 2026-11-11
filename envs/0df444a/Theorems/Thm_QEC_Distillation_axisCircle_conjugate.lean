-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_conjugate
-- name    : QEC.Distillation.axisCircle_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:55:38.361386+00:00
-- url     : https://prove2.me/theorems/be7f2c56-7ac3-4f90-9e7c-582e953fd3e7
-- title:
--   Distillation: axis Circle conjugate
-- statement:
--   Conjugating a Pauli-axis circle transports it along a supplied Pauli transport equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L278-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L278-L297

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_conjugate
    (V : SingleQubitGate) (axis axis' : UnitBlochAxis)
    (haxis : (V : SingleQubitMatrix) * axisPauliMatrix axis *
        ((V⁻¹ : SingleQubitGate) : SingleQubitMatrix) = axisPauliMatrix axis')
    (t : AddCircle (2 * Real.pi)) :
    V * axisCircle axis t * V⁻¹ = axisCircle axis' t := by sorry
