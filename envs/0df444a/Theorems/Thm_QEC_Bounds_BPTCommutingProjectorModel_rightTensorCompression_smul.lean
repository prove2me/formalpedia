-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightTensorCompression_smul
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightTensorCompression_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:09:45.51234+00:00
-- url     : https://prove2.me/theorems/9bfc0d83-8e4a-4830-bad9-55473a71ce61
-- title:
--   BPTCommuting Projector Model: right Tensor Compression smul
-- statement:
--   Compression is linear in the ambient block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualScalar.lean#L24-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualScalar.lean#L24-L32

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualScalar
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.rightTensorCompression_smul
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (eta : B) (scalar : Complex) (T : Semantics.Operator (Semantics.CompositeSystem A B)) :
    rightTensorCompression eta (scalar • T) = scalar • rightTensorCompression eta T := by sorry
