-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_singleQubitLift_mem_generatedUnitaryTopologicalClosure
-- name    : QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_mem_generatedUnitaryTopologicalClosure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:25:23.570994+00:00
-- url     : https://prove2.me/theorems/7affd296-71e8-459d-a23f-95bb6d23b824
-- title:
--   Finite Register Universality: single Qubit Lift mem generated Unitary Topological Closure
-- statement:
--   A closure representative of a one-qubit gate remains a closure
--   representative after the continuous concrete local lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L358-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L358-L366

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

theorem QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_mem_generatedUnitaryTopologicalClosure
    (generators : Set (UnitaryGate (Fin 2))) (wire : Wire)
    {gate : UnitaryGate (Fin 2)}
    (hgate : gate ∈ generatedUnitaryTopologicalClosure generators) :
    singleQubitLift wire gate ∈
      generatedUnitaryTopologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators) := by sorry
