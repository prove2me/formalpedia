-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_oneQubit
-- name    : QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_oneQubit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:58:14.911919+00:00
-- url     : https://prove2.me/theorems/f601a3df-453e-4bfc-8f53-e0ffece7ea92
-- title:
--   Finite Register Circuit: unitary one Qubit
-- statement:
--   The Finite Register Circuit construction uses the unitary one Qubit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L393-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L393-L396

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

theorem QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_oneQubit (wire : Wire) (gate : UnitaryGate (Fin 2)) :
    (oneQubit wire gate : FiniteRegisterCircuit Wire).unitary =
      singleQubitLift wire gate := by sorry

attribute [defeq] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_oneQubit
