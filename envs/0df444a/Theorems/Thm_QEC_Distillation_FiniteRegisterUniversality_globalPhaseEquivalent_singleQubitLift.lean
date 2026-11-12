-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_globalPhaseEquivalent_singleQubitLift
-- name    : QEC.Distillation.FiniteRegisterUniversality.globalPhaseEquivalent_singleQubitLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:24:28.928786+00:00
-- url     : https://prove2.me/theorems/0cb44b88-3517-47d5-9827-8fcbc2f86686
-- title:
--   Finite Register Universality: global Phase Equivalent single Qubit Lift
-- statement:
--   Lifting a global phase on a one-qubit gate gives the same global phase on
--   the finite register.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L193-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L193-L208

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

theorem QEC.Distillation.FiniteRegisterUniversality.globalPhaseEquivalent_singleQubitLift (wire : Wire)
    {left right : UnitaryGate (Fin 2)}
    (hphase : GlobalPhaseEquivalent left right) :
    GlobalPhaseEquivalent (singleQubitLift wire left) (singleQubitLift wire right) := by sorry
