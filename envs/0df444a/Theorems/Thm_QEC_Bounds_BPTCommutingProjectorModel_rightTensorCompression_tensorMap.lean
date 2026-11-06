-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightTensorCompression_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightTensorCompression_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:06:44.004191+00:00
-- url     : https://prove2.me/theorems/4330420d-ea15-4b6a-9763-eec22dbf3ea3
-- title:
--   BPTCommuting Projector Model: right Tensor Compression tensor Map
-- statement:
--   Contracting a tensor block against an arbitrary right-factor vector records
--   the corresponding matrix coefficient on the left.  This is the concrete
--   operation used below to isolate the residual `Theta_{B'' C'}` block after the
--   first- and second-cut decompositions have been identified.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L29-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L29-L42

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rightTensorCompression_tensorMap
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (eta : B) :
    rightTensorCompression eta (TensorProduct.map P Q) =
      (inner Complex eta (Q eta)) • P := by sorry
