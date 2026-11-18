-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalProductTransport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalProductTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:12:57.078232+00:00
-- url     : https://prove2.me/theorems/c2d081ee-f528-4469-b48c-aa11b600059e
-- title:
--   BPTCommuting Projector Model: final Product Transport
-- statement:
--   Abstract algebra behind the two fixed active transports in final assembly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L524-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L524-L551

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

theorem QEC.Bounds.BPTCommutingProjectorModel.finalProductTransport
    {A N X R : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [Semantics.FiniteQuantumSystem R]
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem N X)
      (Semantics.CompositeSystem N X))
    (phi : A) (Q : Semantics.Operator (Semantics.CompositeSystem N
      (Semantics.CompositeSystem X R)))
    (Z : Semantics.Operator (Semantics.CompositeSystem A
      (Semantics.CompositeSystem (Semantics.CompositeSystem N X) R)))
    (n0 : N) (c0 : X) (P : Semantics.Operator R)
    (hjoint : Z = (unitaryLTensor A (tensorAssociatorUnitary N X R).symm).conjOperator
      (rankOneTensorOperator phi Q))
    (hproduct : (unitaryRTensor U R).conjOperator
      ((tensorAssociatorUnitary N X R).symm.conjOperator Q) =
        TensorProduct.map (InnerProductSpace.rankOne Complex
          (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap P) :
    (unitaryLTensor A (unitaryRTensor U R)).conjOperator Z =
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex
          (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap P) := by sorry
