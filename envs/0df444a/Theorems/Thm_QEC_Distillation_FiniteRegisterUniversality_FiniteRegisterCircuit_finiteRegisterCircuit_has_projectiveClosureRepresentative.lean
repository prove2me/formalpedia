-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_finiteRegisterCircuit_has_projectiveClosureRepresentative
-- name    : QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.finiteRegisterCircuit_has_projectiveClosureRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:25:01.660711+00:00
-- url     : https://prove2.me/theorems/ac3a61b9-d790-4e9b-809f-f48a7b7d6be3
-- title:
--   Finite Register Circuit: finite Register Circuit has projective Closure Representative
-- statement:
--   Every explicit circuit has a representative in the register generated
--   closure, modulo one register-global phase, whenever the one-qubit source set
--   is projectively dense.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L410-L448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L410-L448

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
open QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]

theorem QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.finiteRegisterCircuit_has_projectiveClosureRepresentative
    (generators : Set (UnitaryGate (Fin 2)))
    (hdense : ProjectivelyGeneratedDense generators)
    (circuit : FiniteRegisterCircuit Wire) :
    ∃ representative : UnitaryGate (Bitstring Wire),
      representative ∈ generatedUnitaryTopologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators) ∧
      GlobalPhaseEquivalent circuit.unitary representative := by sorry
