-- Prove2me | Theorems.Thm_QEC_Distillation_axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
-- name    : QEC.Distillation.axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:10:02.0487+00:00
-- url     : https://prove2.me/theorems/e4b04e9d-a48b-4b24-9029-24d4a124a27e
-- title:
--   Distillation: axis Circle SU mem special Unitary Generated Closure of irrational word
-- statement:
--   An irrational generated axis word puts the whole special-unitary axis circle in closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L73-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L73-L106

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
    (generators : Set SingleQubitGate) (axis : UnitBlochAxis) (theta : ℝ)
    (word : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi))) :
    ∀ t : AddCircle (2 * Real.pi),
      axisCircleSU axis t ∈ specialUnitaryGeneratedClosure generators := by sorry
