-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_singleQubitLift_mem_finiteRegisterGenerators
-- name    : QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_mem_finiteRegisterGenerators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:24:50.913202+00:00
-- url     : https://prove2.me/theorems/4a3ac178-f192-414e-9159-afbb25f81639
-- title:
--   Finite Register Universality: single Qubit Lift mem finite Register Generators
-- statement:
--   The Finite Register Universality construction uses the single Qubit Lift mem finite Register Generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L318-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L318-L322

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

theorem QEC.Distillation.FiniteRegisterUniversality.singleQubitLift_mem_finiteRegisterGenerators
    (generators : Set (UnitaryGate (Fin 2))) (wire : Wire)
    {gate : UnitaryGate (Fin 2)} (hgate : gate ∈ generators) :
    singleQubitLift wire gate ∈ finiteRegisterGenerators generators := by sorry
