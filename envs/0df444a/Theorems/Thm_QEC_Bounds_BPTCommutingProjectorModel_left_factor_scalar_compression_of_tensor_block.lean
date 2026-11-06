-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_left_factor_scalar_compression_of_tensor_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.left_factor_scalar_compression_of_tensor_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:39:13.607616+00:00
-- url     : https://prove2.me/theorems/7bdf50d7-2bfc-4c9b-80ef-0aff0de5099d
-- title:
--   BPTCommuting Projector Model: left factor scalar compression of tensor block
-- statement:
--   Cancel the nonzero right tensor factor after transporting a compressed scalar
--   equation to a literal product block.  This is the algebraic tail shared by
--   the second-cut `Pi_AB'` and residual-factor scalar-compression arguments.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/TensorFactor.lean#L28-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/TensorFactor.lean#L28-L74

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_TensorFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.left_factor_scalar_compression_of_tensor_block
    {H K S : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S]
    (T : Semantics.UnitaryTransport S (Semantics.CompositeSystem H K))
    (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (R L : Semantics.Operator S) (X : Semantics.Operator H) (scalar : Complex)
    (hblock : T.conjOperator R = TensorProduct.map P Q)
    (hQidem : Q * Q = Q) (hQ0 : Q ≠ 0)
    (hscalar : R * L * R = scalar • R)
    (hprobe : T.conjOperator L =
      TensorProduct.map X (1 : Semantics.Operator K)) :
    P * X * P = scalar • P := by sorry
