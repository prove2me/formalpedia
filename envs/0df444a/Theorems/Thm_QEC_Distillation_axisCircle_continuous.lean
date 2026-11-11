-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_continuous
-- name    : QEC.Distillation.axisCircle_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:10:37.558511+00:00
-- url     : https://prove2.me/theorems/611ed14d-7fc4-44c5-8888-d57dc355585c
-- title:
--   Distillation: axis Circle continuous
-- statement:
--   The axis circle is continuous as a map into the concrete unitary group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L267-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L267-L275

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_continuous (axis : UnitBlochAxis) :
    Continuous (axisCircle axis : AddCircle (2 * Real.pi) → SingleQubitGate) := by sorry
