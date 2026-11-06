-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_idempotent_of_tensor_product_projection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.right_factor_idempotent_of_tensor_product_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:07.969378+00:00
-- url     : https://prove2.me/theorems/e9d68573-78a0-4c90-94ca-a83ecd6cea78
-- title:
--   BPTCommuting Projector Model: right factor idempotent of tensor product projection
-- statement:
--   In a nonzero tensor-block code projection, idempotence of a nonzero left
--   factor forces idempotence of the right factor.  This is the minimal algebra
--   needed to cancel the residual block in the hM scalar-compression argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L152-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L152-L169

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.right_factor_idempotent_of_tensor_product_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (P : Semantics.Operator H) (Q : Semantics.Operator K)
    (hP : P * P = P) (hP0 : P ≠ 0)
    (hPQ : (TensorProduct.map P Q).IsSymmetricProjection) : Q * Q = Q := by sorry
