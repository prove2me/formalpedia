-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_det
-- name    : QEC.Distillation.axisCircle_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:10:06.445048+00:00
-- url     : https://prove2.me/theorems/703fd147-5f85-4678-99b2-ab4453a18cb1
-- title:
--   Distillation: axis Circle det
-- statement:
--   Every axis-circle matrix has determinant one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L182-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L182-L203

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_det (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    (axisCircle axis t : SingleQubitMatrix).det = 1 := by sorry
