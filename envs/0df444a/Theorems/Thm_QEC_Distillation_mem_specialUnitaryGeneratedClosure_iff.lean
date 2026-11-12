-- Prove2me | Theorems.Thm_QEC_Distillation_mem_specialUnitaryGeneratedClosure_iff
-- name    : QEC.Distillation.mem_specialUnitaryGeneratedClosure_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:17:13.808573+00:00
-- url     : https://prove2.me/theorems/f20bd035-5472-42c3-99ba-0985e301dac7
-- title:
--   Distillation: mem special Unitary Generated Closure iff
-- statement:
--   Membership in the special-unitary pullback is ambient generated-closure membership.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L27-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L27-L31

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.mem_specialUnitaryGeneratedClosure_iff
    (generators : Set SingleQubitGate) (U : SingleQubitSpecialUnitary) :
    U ∈ specialUnitaryGeneratedClosure generators ↔
      (U : SingleQubitGate) ∈ generatedUnitaryTopologicalClosure generators := by sorry
