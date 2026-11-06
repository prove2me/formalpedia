-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensor_factor_eq_of_rankOne_joint_block_associator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensor_factor_eq_of_rankOne_joint_block_associator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:07:28.914216+00:00
-- url     : https://prove2.me/theorems/f73c95c0-c0eb-4813-9904-a911a97a76e4
-- title:
--   BPTCommuting Projector Model: tensor factor eq of rank One joint block associator
-- statement:
--   An actual joint rank-one block can be reconstructed through the two source
--   associators without collapsing its arbitrary final projector.  The hypothesis
--   is the literal common active block, and the conclusion is the `hcommon` form
--   consumed by the BPT residual argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L117-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/Tensor.lean#L117-L172

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensor_factor_eq_of_rankOne_joint_block_associator
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (phi : A) (hphi : ‖phi‖ = 1)
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem B C)))
    (Qright : Semantics.Operator (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))
    (P_D : Semantics.Operator D)
    (hjoint :
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright) =
        (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
          (TensorProduct.map Pleft P_D)) :
    (tensorAssociatorUnitary B C D).symm.conjOperator Qright =
      TensorProduct.map (leftTensorCompression phi Pleft) P_D := by sorry
