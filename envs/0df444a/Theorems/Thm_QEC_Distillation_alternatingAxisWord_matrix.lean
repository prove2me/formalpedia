-- Prove2me | Theorems.Thm_QEC_Distillation_alternatingAxisWord_matrix
-- name    : QEC.Distillation.alternatingAxisWord_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:02:54.698202+00:00
-- url     : https://prove2.me/theorems/b2ed0f26-b88f-4c55-8a52-0f61ff64e43d
-- title:
--   Distillation: alternating Axis Word matrix
-- statement:
--   The alternating word has exactly the displayed scalar-plus-vector coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L336-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L336-L350

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.alternatingAxisWord_matrix (axis axis' : UnitBlochAxis) (x y z : Real) :
    (alternatingAxisWord axis axis' x y z : SingleQubitMatrix) =
      su2Matrix (alternatingWordScalar axis axis' x y z)
        (alternatingWordVector axis axis' x y z) := by sorry
