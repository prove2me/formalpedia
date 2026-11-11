-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_continuous_singleQubitLift
-- name    : QEC.Distillation.FiniteRegisterUniversality.continuous_singleQubitLift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:24:27.597888+00:00
-- url     : https://prove2.me/theorems/c2f7bfab-a9cd-4f1d-9756-cd6b828c8cce
-- title:
--   Finite Register Universality: continuous single Qubit Lift
-- statement:
--   The concrete selected-wire lift is continuous in its one-qubit input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L183-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L183-L189

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteRegisterUniversality
open Semantics Semantics.Qubit
open GeneratedUniversality
open scoped Kronecker
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]

theorem QEC.Distillation.FiniteRegisterUniversality.continuous_singleQubitLift (wire : Wire) :
    Continuous (singleQubitLift wire) := by sorry
