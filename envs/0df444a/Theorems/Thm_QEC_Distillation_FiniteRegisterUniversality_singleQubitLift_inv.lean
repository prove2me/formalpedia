-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_singleQubitLift_inv
-- name    : QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:24:11.2799+00:00
-- url     : https://prove2.me/theorems/e695ee8f-0bcf-4c66-b058-42e9e8765a81
-- title:
--   Finite Register Universality: single Qubit Lift inv
-- statement:
--   The local lift preserves inversion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L178-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L178-L180

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

theorem QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_inv (wire : Wire) (gate : UnitaryGate (Fin 2)) :
    singleQubitLift wire gate⁻¹ = (singleQubitLift wire gate)⁻¹ := by sorry
