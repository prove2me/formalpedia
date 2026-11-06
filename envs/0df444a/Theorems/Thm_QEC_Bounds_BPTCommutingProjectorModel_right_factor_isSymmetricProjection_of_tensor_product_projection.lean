-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_isSymmetricProjection_of_tensor_product_projection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.right_factor_isSymmetricProjection_of_tensor_product_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:08:48.312262+00:00
-- url     : https://prove2.me/theorems/f9452577-b863-4448-a353-a6f3d55410f8
-- title:
--   BPTCommuting Projector Model: right factor is Symmetric Projection of tensor product projection
-- statement:
--   A nonzero projection factor transfers projection structure to `Theta`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L105-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L105-L131

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.right_factor_isSymmetricProjection_of_tensor_product_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hprojection : (TensorProduct.map P Q).IsSymmetricProjection) :
    Q.IsSymmetricProjection := by sorry
