-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_rightTensorExtensionAfterLeft
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_rightTensorExtensionAfterLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:26:25.930816+00:00
-- url     : https://prove2.me/theorems/6f2de55b-9111-4140-b7e6-46a5c185b0d9
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection of right Tensor Extension After Left
-- statement:
--   A right-tensor extension is a projection only if its left tensor factor is one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3740-L3751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3740-L3751

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_rightTensorExtensionAfterLeft
    {A W N : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (h : (rightTensorExtensionAfterLeft A W N P).IsSymmetricProjection) :
    (TensorProduct.map P (1 : Semantics.Operator N)).IsSymmetricProjection := by sorry
