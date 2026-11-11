-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_matrix_entries
-- name    : QEC.Distillation.axisCircle_matrix_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:55:07.942204+00:00
-- url     : https://prove2.me/theorems/5e6dd4b9-bbca-4089-92bb-4e87a4e676fb
-- title:
--   Distillation: axis Circle matrix entries
-- statement:
--   Exact matrix entries for the axis circle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L163-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L163-L179

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_matrix_entries (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    (axisCircle axis t : SingleQubitMatrix) =
      !![((AddCircle.toCircle t : Complex).re : Complex) -
          Complex.I * ((AddCircle.toCircle t : Complex).im : Complex) * (axis.z : Complex),
         -Complex.I * ((AddCircle.toCircle t : Complex).im : Complex) * (axis.x : Complex) -
          ((AddCircle.toCircle t : Complex).im : Complex) * (axis.y : Complex);
         -Complex.I * ((AddCircle.toCircle t : Complex).im : Complex) * (axis.x : Complex) +
          ((AddCircle.toCircle t : Complex).im : Complex) * (axis.y : Complex),
         ((AddCircle.toCircle t : Complex).re : Complex) +
          Complex.I * ((AddCircle.toCircle t : Complex).im : Complex) * (axis.z : Complex)] := by sorry
