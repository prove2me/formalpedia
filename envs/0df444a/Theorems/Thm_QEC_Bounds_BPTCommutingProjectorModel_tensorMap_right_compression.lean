-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_right_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorMap_right_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:29:41.624812+00:00
-- url     : https://prove2.me/theorems/29531690-8ff7-4838-a7e1-b06bc5778529
-- title:
--   BPTCommuting Projector Model: tensor Map right compression
-- statement:
--   Compressing the right factor of a tensor block leaves its left factor unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L240-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L240-L252

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorMap_right_compression
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (K : C →ₗ[Complex] B) :
    (LinearMap.adjoint (TensorProduct.map (1 : Semantics.Operator A) K)).comp
        ((TensorProduct.map P Q).comp (TensorProduct.map (1 : Semantics.Operator A) K)) =
      TensorProduct.map P ((LinearMap.adjoint K).comp (Q.comp K)) := by sorry
