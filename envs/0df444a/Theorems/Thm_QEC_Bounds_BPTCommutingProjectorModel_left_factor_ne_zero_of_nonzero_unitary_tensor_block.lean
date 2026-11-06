-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_left_factor_ne_zero_of_nonzero_unitary_tensor_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.left_factor_ne_zero_of_nonzero_unitary_tensor_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:22.136215+00:00
-- url     : https://prove2.me/theorems/12f7453d-925a-4146-8763-3c52ac7f9391
-- title:
--   BPTCommuting Projector Model: left factor ne zero of nonzero unitary tensor block
-- statement:
--   A nonzero operator remains nonzero when its unitary block is a tensor map with nonzero left factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L133-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L133-L156

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.left_factor_ne_zero_of_nonzero_unitary_tensor_block
    {X A W N C : Type u}
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.UnitaryTransport X
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem N C)))
    (R : Semantics.Operator X)
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator (Semantics.CompositeSystem N C))
    (hR : R ≠ 0) (hblock : T.conjOperator R = TensorProduct.map P Q) :
    P ≠ 0 := by sorry
