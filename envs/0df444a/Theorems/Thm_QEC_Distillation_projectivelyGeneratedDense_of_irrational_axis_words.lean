-- Prove2me | Theorems.Thm_QEC_Distillation_projectivelyGeneratedDense_of_irrational_axis_words
-- name    : QEC.Distillation.projectivelyGeneratedDense_of_irrational_axis_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:04:48.803329+00:00
-- url     : https://prove2.me/theorems/2a2c5d76-dbb5-45f8-afaf-f41dca79fbca
-- title:
--   Distillation: projectively Generated Dense of irrational axis words
-- statement:
--   Two nonparallel irrational generated axis words are projectively dense.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L109-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L109-L135

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.projectivelyGeneratedDense_of_irrational_axis_words
    (generators : Set SingleQubitGate) (axis axis' : UnitBlochAxis) (theta : ℝ)
    (word word' : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (hword' : word' ∈ generatedUnitarySubgroup generators)
    (hword'_eq : word' = axisCircle axis' (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi)))
    (hnonparallel : axis.Nonparallel axis') :
    ProjectivelyGeneratedDense generators := by sorry
