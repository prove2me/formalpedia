-- Prove2me | Theorems.Thm_QEC_Distillation_isClosed_specialUnitaryGeneratedClosure
-- name    : QEC.Distillation.isClosed_specialUnitaryGeneratedClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:04:43.330183+00:00
-- url     : https://prove2.me/theorems/627e2d1b-0e3e-4e04-897e-35da9c92cf04
-- title:
--   Distillation: is Closed special Unitary Generated Closure
-- statement:
--   The special-unitary pullback of the ambient generated closure is closed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L34-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L34-L41

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.isClosed_specialUnitaryGeneratedClosure
    (generators : Set SingleQubitGate) :
    IsClosed (specialUnitaryGeneratedClosure generators : Set SingleQubitSpecialUnitary) := by sorry
