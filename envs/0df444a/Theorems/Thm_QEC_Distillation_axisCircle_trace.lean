-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_trace
-- name    : QEC.Distillation.axisCircle_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:57:51.903021+00:00
-- url     : https://prove2.me/theorems/92b6d223-8cd8-4e91-a5c4-afb70bfccf88
-- title:
--   Distillation: axis Circle trace
-- statement:
--   The trace recovers twice the real circle coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L206-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L206-L211

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_trace (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    Matrix.trace (axisCircle axis t : SingleQubitMatrix) =
      2 * ((AddCircle.toCircle t : Complex).re : Complex) := by sorry
