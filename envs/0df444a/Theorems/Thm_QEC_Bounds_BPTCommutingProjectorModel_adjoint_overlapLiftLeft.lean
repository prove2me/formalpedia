-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapLiftLeft
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLiftLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:55:38.335991+00:00
-- url     : https://prove2.me/theorems/59c75a3c-b5f0-4146-b9dc-6d655736bd6a
-- title:
--   BPTCommuting Projector Model: adjoint overlap Lift Left
-- statement:
--   Taking an adjoint commutes with the left overlap lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3069-L3077
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3069-L3077

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLiftLeft
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) :
    LinearMap.adjoint (overlapLiftLeft (C := C) P) =
      overlapLiftLeft (C := C) (LinearMap.adjoint P) := by sorry
