-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commonFactorization_of_transport_equivalent_blocks
-- name    : QEC.Bounds.BPTCommutingProjectorModel.commonFactorization_of_transport_equivalent_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:08:12.654037+00:00
-- url     : https://prove2.me/theorems/de1dffc8-a07e-4ce0-87fd-3810aaf3818d
-- title:
--   BPTCommuting Projector Model: common Factorization of transport equivalent blocks
-- statement:
--   Transport-compatible realizations of one operator block determine the common
--   rank-one factorization.  This isolates the model-independent transport step
--   from the large BPT sector types used to instantiate it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/TransportFactorizationCore.lean#L26-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/TransportFactorizationCore.lean#L26-L75

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Compression
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_TransportFactorizationCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Bounds.BPTCommutingProjectorModel

theorem QEC.Bounds.BPTCommutingProjectorModel.commonFactorization_of_transport_equivalent_blocks
    {X Y A B C D : Type u}
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup Y] [InnerProductSpace Complex Y] [Semantics.FiniteQuantumSystem Y]
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (V : Semantics.UnitaryTransport X Y)
    (Gsecond : Semantics.UnitaryTransport Y
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)))
    (Gfirst : Semantics.UnitaryTransport X
      (Semantics.CompositeSystem A
        (Semantics.CompositeSystem (Semantics.CompositeSystem B C) D)))
    (Rsecond : Semantics.Operator Y) (Rfirst : Semantics.Operator X)
    (phi : A) (hphi : ‖phi‖ = 1)
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B C)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))
    (P_D : Semantics.Operator D)
    (hsequential : Rsecond = V.conjOperator Rfirst)
    (htransport : composeUnitaryTransport V Gsecond = Gfirst)
    (hsecond :
      Gsecond.conjOperator Rsecond =
        (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright))
    (hfirst :
      Gfirst.conjOperator Rfirst =
        (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
          (TensorProduct.map Pleft P_D)) :
    (tensorAssociatorUnitary B C D).symm.conjOperator Qright =
      TensorProduct.map (leftTensorCompression phi Pleft) P_D := by sorry
