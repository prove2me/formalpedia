-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:32.438578+00:00
-- url     : https://prove2.me/theorems/9c008351-042b-4cfd-8d62-a43b7f0a1c28
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift is Symmetric Projection
-- statement:
--   The literal second-cut code lift is an orthogonal projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L60-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L60-L74

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCodeLift region).IsSymmetricProjection := by sorry
