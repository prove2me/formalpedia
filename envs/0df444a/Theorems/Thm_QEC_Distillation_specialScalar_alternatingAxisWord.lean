-- Prove2me | Theorems.Thm_QEC_Distillation_specialScalar_alternatingAxisWord
-- name    : QEC.Distillation.specialScalar_alternatingAxisWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:03:07.052997+00:00
-- url     : https://prove2.me/theorems/58be6a06-c112-46d8-9922-40afe895ac14
-- title:
--   Distillation: special Scalar alternating Axis Word
-- statement:
--   The scalar coordinate of an alternating word is the displayed word scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L728-L733
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L728-L733

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.specialScalar_alternatingAxisWord (axis axis' : UnitBlochAxis) (x y z : Real) :
    specialScalar (alternatingAxisWord axis axis' x y z) =
      alternatingWordScalar axis axis' x y z := by sorry
