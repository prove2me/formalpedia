-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_eq_of_common_isometric_factorization_under_unitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.eq_of_common_isometric_factorization_under_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:13:48.009209+00:00
-- url     : https://prove2.me/theorems/6ec974b1-d4e3-4d52-9dce-7d132182202a
-- title:
--   BPTCommuting Projector Model: eq of common isometric factorization under unitary
-- statement:
--   Pull a common isometric factorization back through a unitary coordinate change.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L331-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L331-L350

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.eq_of_common_isometric_factorization_under_unitary
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (F : Semantics.UnitaryTransport H K)
    (A B : Semantics.Operator H) (P : Semantics.Operator S)
    (Eout Eleft : S →ₗ[Complex] K)
    (hA : F.conjOperator A = Eout.comp (P.comp (LinearMap.adjoint Eout)))
    (hE : Eleft = Eout)
    (hB : F.conjOperator B = Eleft.comp (P.comp (LinearMap.adjoint Eleft))) :
    A = B := by sorry
