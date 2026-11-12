-- Prove2me | Theorems.Thm_QEC_Distillation_finitePrecisionOneQubitUniversal_of_irrational_axis_words
-- name    : QEC.Distillation.finitePrecisionOneQubitUniversal_of_irrational_axis_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:04:38.029024+00:00
-- url     : https://prove2.me/theorems/20f36964-12c5-4e34-84fd-094f6d8fa927
-- title:
--   Distillation: finite Precision One Qubit Universal of irrational axis words
-- statement:
--   The projective-density criterion yields finite-precision one-qubit universality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L138-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean#L138-L150

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality

theorem QEC.Distillation.finitePrecisionOneQubitUniversal_of_irrational_axis_words
    (generators : Set SingleQubitGate) (axis axis' : UnitBlochAxis) (theta : ℝ)
    (word word' : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (hword' : word' ∈ generatedUnitarySubgroup generators)
    (hword'_eq : word' = axisCircle axis' (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi)))
    (hnonparallel : axis.Nonparallel axis') :
    FinitePrecisionOneQubitUniversal generators := by sorry
