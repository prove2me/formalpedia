-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_axis_recovery
-- name    : QEC.Distillation.axisCircle_axis_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:58:09.829865+00:00
-- url     : https://prove2.me/theorems/35b9a913-0fa8-4e3e-86f8-defc44cd7711
-- title:
--   Distillation: axis Circle axis recovery
-- statement:
--   A nontrivial axis-circle point determines its transparent unit Bloch axis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L230-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L230-L235

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_axis_recovery {axis axis' : UnitBlochAxis}
    (t : AddCircle (2 * Real.pi))
    (h_im : (AddCircle.toCircle t : Complex).im ≠ 0)
    (hgate : axisCircle axis t = axisCircle axis' t) : axis = axis' := by sorry
