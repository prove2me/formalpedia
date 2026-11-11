-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
-- name    : QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T15:02:58.315757+00:00
-- url     : https://prove2.me/theorems/1a1c164e-fa07-4537-84bd-4f24835ad617
-- title:
--   Finite Register Circuit: finite Register Circuit approximates of projectively Generated Dense
-- statement:
--   The projective closure representative of an explicit circuit yields a
--   finite-precision approximation at every positive requested precision.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L452-L462
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L452-L462

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

theorem QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
    (generators : Set (UnitaryGate (Fin 2)))
    (hdense : ProjectivelyGeneratedDense generators)
    (circuit : FiniteRegisterCircuit Wire) (precision : Real) (hprecision : 0 < precision) :
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) generators) circuit.unitary precision := by sorry
