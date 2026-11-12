-- Prove2me | Theorems.Thm_QEC_Distillation_UnitBlochAxis_nonparallel_pauli_commutator_ne_zero
-- name    : QEC.Distillation.UnitBlochAxis.nonparallel_pauli_commutator_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:14:50.797293+00:00
-- url     : https://prove2.me/theorems/8c1a0d37-631b-4cd5-a0f7-0d2e65894a8e
-- title:
--   Unit Bloch Axis: nonparallel pauli commutator ne zero
-- statement:
--   Nonparallel axes have a nonzero Pauli commutator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L105-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean#L105-L138

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix

theorem QEC.Distillation.UnitBlochAxis.nonparallel_pauli_commutator_ne_zero
    {axis axis' : UnitBlochAxis} (h : axis.Nonparallel axis') :
    axisPauliMatrix axis * axisPauliMatrix axis' -
        axisPauliMatrix axis' * axisPauliMatrix axis ≠ 0 := by sorry
