-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_left_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorMap_left_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:25.784964+00:00
-- url     : https://prove2.me/theorems/418c0005-bfc4-40bf-9c96-0c9b4f024e38
-- title:
--   BPTCommuting Projector Model: tensor Map left compression
-- statement:
--   Compressing the left factor of a tensor block leaves its right factor unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L255-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L255-L267

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorMap_left_compression
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (K : C →ₗ[Complex] A) :
    (LinearMap.adjoint (TensorProduct.map K (1 : Semantics.Operator B))).comp
        ((TensorProduct.map P Q).comp (TensorProduct.map K (1 : Semantics.Operator B))) =
      TensorProduct.map ((LinearMap.adjoint K).comp (P.comp K)) Q := by sorry
