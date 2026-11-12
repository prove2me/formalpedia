-- Prove2me | Theorems.Thm_QEC_Distillation_subgroup_isOpen_of_contains_nonparallel_axisCircles
-- name    : QEC.Distillation.subgroup_isOpen_of_contains_nonparallel_axisCircles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:09:01.235566+00:00
-- url     : https://prove2.me/theorems/9b76a678-b82d-4424-a565-26fb99e05ac5
-- title:
--   Distillation: subgroup is Open of contains nonparallel axis Circles
-- statement:
--   A subgroup containing two nonparallel complete axis circles is open.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L844-L876
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L844-L876

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.subgroup_isOpen_of_contains_nonparallel_axisCircles
    (K : Subgroup SingleQubitSpecialUnitary) (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K) :
    IsOpen (K : Set SingleQubitSpecialUnitary) := by sorry
