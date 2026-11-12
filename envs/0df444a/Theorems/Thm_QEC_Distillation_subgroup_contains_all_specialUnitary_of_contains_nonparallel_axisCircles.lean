-- Prove2me | Theorems.Thm_QEC_Distillation_subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles
-- name    : QEC.Distillation.subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:09:20.870631+00:00
-- url     : https://prove2.me/theorems/58c856b0-af7a-4fee-a281-6d185351218a
-- title:
--   Distillation: subgroup contains all special Unitary of contains nonparallel axis Circles
-- statement:
--   Two nonparallel complete axis circles generate every determinant-one special unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L996-L1013
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L996-L1013

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles
    (K : Subgroup SingleQubitSpecialUnitary) (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K)
    (U : SingleQubitSpecialUnitary) : U ∈ K := by sorry
