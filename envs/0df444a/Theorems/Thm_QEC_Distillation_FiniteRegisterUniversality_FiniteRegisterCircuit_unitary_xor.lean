-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_xor
-- name    : QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_xor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:59:14.950671+00:00
-- url     : https://prove2.me/theorems/58ee5a09-c952-45fa-a3b0-b231a4a8300a
-- title:
--   Finite Register Circuit: unitary xor
-- statement:
--   The Finite Register Circuit construction uses the unitary xor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L398-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L398-L401

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

theorem QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_xor (control target : Wire) (hdistinct : control ≠ target) :
    (xor control target hdistinct : FiniteRegisterCircuit Wire).unitary =
      registerXorGate control target hdistinct := by sorry

attribute [defeq] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_xor
