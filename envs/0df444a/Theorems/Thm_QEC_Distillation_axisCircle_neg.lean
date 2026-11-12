-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircle_neg
-- name    : QEC.Distillation.axisCircle_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:58:09.252427+00:00
-- url     : https://prove2.me/theorems/cc127da4-216c-4691-a2cb-c944531b39a9
-- title:
--   Distillation: axis Circle neg
-- statement:
--   Negating a circle parameter gives the inverse unitary gate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L252-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean#L252-L256

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircle_neg (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    axisCircle axis (-t) = (axisCircle axis t)⁻¹ := by sorry
