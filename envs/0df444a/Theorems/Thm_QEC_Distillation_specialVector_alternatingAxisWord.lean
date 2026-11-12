-- Prove2me | Theorems.Thm_QEC_Distillation_specialVector_alternatingAxisWord
-- name    : QEC.Distillation.specialVector_alternatingAxisWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:04:30.967339+00:00
-- url     : https://prove2.me/theorems/b4402f5a-eb5c-45b6-b615-0feafb6ea5e3
-- title:
--   Distillation: special Vector alternating Axis Word
-- statement:
--   The vector coordinate of an alternating word is the displayed word vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L736-L744
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L736-L744

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.specialVector_alternatingAxisWord (axis axis' : UnitBlochAxis) (x y z : Real) :
    specialVector (alternatingAxisWord axis axis' x y z) =
      alternatingWordVector axis axis' x y z := by sorry
