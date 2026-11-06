-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_mul_BC_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:23.132605+00:00
-- url     : https://prove2.me/theorems/cb71f67d-e2be-409f-b045-b254751d07bd
-- title:
--   BPTCommuting Projector Model: projector AB mul BC is Symmetric Projection
-- statement:
--   The `MC` source grouped projector is an actual orthogonal projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2603-L2609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2603-L2609

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.projectorAB region * M.projectorBC region).IsSymmetricProjection := by sorry
