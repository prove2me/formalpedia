-- Prove2me | Theorems.Thm_QEC_Distillation_closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
-- name    : QEC.Distillation.closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:09:28.335917+00:00
-- url     : https://prove2.me/theorems/b7f592ec-e1fe-406f-8e74-6b62f3d1d2bb
-- title:
--   Distillation: closed Subgroup eq top of contains nonparallel axis Circles
-- statement:
--   The closed-subgroup form needed by the next determinant-one generation layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L1016-L1026
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L1016-L1026

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
    (K : Subgroup SingleQubitSpecialUnitary)
    (_hclosed : IsClosed (K : Set SingleQubitSpecialUnitary))
    (axis axis' : UnitBlochAxis) (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K) :
    K = ⊤ := by sorry
