-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftTensorCompression_tensorAssociator_conj_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.leftTensorCompression_tensorAssociator_conj_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:07:06.584557+00:00
-- url     : https://prove2.me/theorems/6f63b17c-b4ab-43e3-9976-d50c5c1e1af4
-- title:
--   BPTCommuting Projector Model: left Tensor Compression tensor Associator conj tensor Map
-- statement:
--   Left compression commutes with reassociating a tensor block, while preserving
--   the arbitrary right factor.  This is the associator-aware coefficient identity
--   needed to retain the BPT source projector `Pi_C''D` unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L65-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L65-L109

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

theorem QEC.Bounds.BPTCommutingProjectorModel.leftTensorCompression_tensorAssociator_conj_tensorMap
    {A W N : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (eta : A) (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator N) :
    leftTensorCompression eta
      ((tensorAssociatorUnitary A W N).conjOperator (TensorProduct.map P Q)) =
      TensorProduct.map (leftTensorCompression eta P) Q := by sorry
