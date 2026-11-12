-- Prove2me | Theorems.Thm_QEC_Distillation_alternatingAxisWord_mem
-- name    : QEC.Distillation.alternatingAxisWord_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:04:17.104338+00:00
-- url     : https://prove2.me/theorems/cb23b920-2880-4a34-a35b-416d29c2f4c6
-- title:
--   Distillation: alternating Axis Word mem
-- statement:
--   Every finite alternating word belongs to a subgroup containing both full circles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L324-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L324-L333

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.alternatingAxisWord_mem (K : Subgroup SingleQubitSpecialUnitary)
    (axis axis' : UnitBlochAxis)
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K)
    (x y z : Real) : alternatingAxisWord axis axis' x y z ∈ K := by sorry
