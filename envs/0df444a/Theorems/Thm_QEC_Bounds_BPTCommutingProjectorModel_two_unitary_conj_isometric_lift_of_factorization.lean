-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_two_unitary_conj_isometric_lift_of_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.two_unitary_conj_isometric_lift_of_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-18T04:13:49.750405+00:00
-- url     : https://prove2.me/theorems/388a0caa-19eb-4632-b023-432c976c5e02
-- title:
--   BPTCommuting Projector Model: two unitary conj isometric lift of factorization
-- statement:
--   Transport an already factored isometric lift through two unitary coordinate
--   changes without reopening the concrete operator definitions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L292-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L292-L312

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

theorem QEC.Bounds.BPTCommutingProjectorModel.two_unitary_conj_isometric_lift_of_factorization
    {S H K R : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [Semantics.FiniteQuantumSystem R]
    (Tinner : Semantics.UnitaryTransport H K)
    (Touter : Semantics.UnitaryTransport K R)
    (J : S →ₗ[Complex] H) (P : Semantics.Operator S)
    (Q : Semantics.Operator H)
    (E : S →ₗ[Complex] R)
    (hQ : Q = J.comp (P.comp (LinearMap.adjoint J)))
    (hE : Touter.toLinearEquiv.toLinearMap.comp
        (Tinner.toLinearEquiv.toLinearMap.comp J) = E) :
    Touter.conjOperator (Tinner.conjOperator Q) =
      E.comp (P.comp (LinearMap.adjoint E)) := by sorry
