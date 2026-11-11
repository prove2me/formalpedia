-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_registerXorGate_matrix
-- name    : QEC.Distillation.FiniteRegisterUniversality.registerXorGate_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:21:11.357591+00:00
-- url     : https://prove2.me/theorems/de133bee-ef0e-4f0e-b714-61c76e943a1d
-- title:
--   Finite Register Universality: register Xor Gate matrix
-- statement:
--   The gate and transport share exactly the same explicit basis permutation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L284-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L284-L289

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

theorem QEC.Distillation.FiniteRegisterUniversality.registerXorGate_matrix (control target : Wire)
    (hdistinct : control ≠ target) :
    (registerXorGate control target hdistinct :
      Matrix (Bitstring Wire) (Bitstring Wire) Complex) =
      (registerXorBitstringEquiv control target hdistinct).permMatrix Complex := by sorry

attribute [defeq] QEC.Distillation.FiniteRegisterUniversality.registerXorGate_matrix
