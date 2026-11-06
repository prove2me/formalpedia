-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_isSymmetricProjection_of_rankOne_tensor_projection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.right_factor_isSymmetricProjection_of_rankOne_tensor_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:54:18.796514+00:00
-- url     : https://prove2.me/theorems/41f31ab6-fc31-4d9f-b645-a187f807816d
-- title:
--   BPTCommuting Projector Model: right factor is Symmetric Projection of rank One tensor projection
-- statement:
--   When a nonzero normalized rank-one left factor tensors with an orthogonal
--   projection, the right factor is itself an orthogonal projection.  This turns
--   the second-cut residual into the concrete code projector to which the two
--   residual erasure arguments are applied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/RightProjection.lean#L29-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/RightProjection.lean#L29-L84

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RightProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.right_factor_isSymmetricProjection_of_rankOne_tensor_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (hprojection :
      LinearMap.IsSymmetricProjection
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q)) :
    LinearMap.IsSymmetricProjection Q := by sorry
