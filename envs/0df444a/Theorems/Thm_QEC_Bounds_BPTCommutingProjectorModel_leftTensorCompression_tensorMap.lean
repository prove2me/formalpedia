-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftTensorCompression_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftTensorCompression_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:07:02.895767+00:00
-- url     : https://prove2.me/theorems/f87a1600-aaa4-44be-8cd9-ce96fa9197a7
-- title:
--   BPTCommuting Projector Model: left Tensor Compression tensor Map
-- statement:
--   Contracting a tensor-product operator against its left factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L45-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L45-L58

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalResidual
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.leftTensorCompression_tensorMap
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (eta : A) :
    leftTensorCompression eta (TensorProduct.map P Q) =
      (inner Complex eta (P eta)) • Q := by sorry
