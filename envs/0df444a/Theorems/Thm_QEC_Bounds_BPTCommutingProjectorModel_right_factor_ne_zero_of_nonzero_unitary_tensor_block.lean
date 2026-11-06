-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_ne_zero_of_nonzero_unitary_tensor_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.right_factor_ne_zero_of_nonzero_unitary_tensor_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:37:16.597389+00:00
-- url     : https://prove2.me/theorems/357a0946-11f9-49db-a56f-e35cfeb3ffd8
-- title:
--   BPTCommuting Projector Model: right factor ne zero of nonzero unitary tensor block
-- statement:
--   A nonzero tensor block has a nonzero right factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/TensorFactor.lean#L77-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/TensorFactor.lean#L77-L94

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

theorem QEC.Bounds.BPTCommutingProjectorModel.right_factor_ne_zero_of_nonzero_unitary_tensor_block
    {S H K : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport S (Semantics.CompositeSystem H K))
    (R : Semantics.Operator S) (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hR : R ≠ 0) (hblock : T.conjOperator R = TensorProduct.map P Q) : Q ≠ 0 := by sorry
