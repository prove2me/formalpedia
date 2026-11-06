-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conjOperator_productBlockRegrouping
-- name    : QEC.Bounds.BPTCommutingProjectorModel.conjOperator_productBlockRegrouping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:27:30.120325+00:00
-- url     : https://prove2.me/theorems/7d8eb0fe-92ca-441e-a01f-3a9812c993ba
-- title:
--   BPTCommuting Projector Model: conj Operator product Block Regrouping
-- statement:
--   Regroup a product rank-one block past an arbitrary operator on the final factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L78-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L78-L179

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.conjOperator_productBlockRegrouping
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (phi : Semantics.CompositeSystem A W) (n0 : N) (c0 : X) (P_D : Semantics.Operator D) :
    productBlockRegrouping.conjOperator
      (TensorProduct.map
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
        P_D) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex
          (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P_D) := by sorry
