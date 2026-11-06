-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutProjectorAB_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutProjectorAB_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:07.158186+00:00
-- url     : https://prove2.me/theorems/2cadd9ed-adaa-446b-a95a-e6f83ae74689
-- title:
--   BPTCommuting Projector Model: second Cut Projector AB is Symmetric Projection
-- statement:
--   The literal `AB` projector of the second cut is an orthogonal projection.
--   This is reflected from the actual physical source projector through the
--   second-cut coordinate transport, not assumed as part of the BV03 package.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L298-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Embedding.lean#L298-L317

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutProjectorAB_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorProjectorABLocal region).IsSymmetricProjection := by sorry
