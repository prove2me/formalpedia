-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_eq_of_common_isometric_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.eq_of_common_isometric_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:12:59.996128+00:00
-- url     : https://prove2.me/theorems/874a1985-0df8-497c-8d08-ef13d2f6f818
-- title:
--   BPTCommuting Projector Model: eq of common isometric factorization
-- statement:
--   Two operators are equal when their factorizations differ only by a named embedding equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L315-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L315-L328

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

theorem QEC.Bounds.BPTCommutingProjectorModel.eq_of_common_isometric_factorization
    {S H : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (A B : Semantics.Operator H) (P : Semantics.Operator S)
    (Eout Eleft : S →ₗ[Complex] H)
    (hA : A = Eout.comp (P.comp (LinearMap.adjoint Eout)))
    (hE : Eleft = Eout)
    (hB : B = Eleft.comp (P.comp (LinearMap.adjoint Eleft))) :
    A = B := by sorry
