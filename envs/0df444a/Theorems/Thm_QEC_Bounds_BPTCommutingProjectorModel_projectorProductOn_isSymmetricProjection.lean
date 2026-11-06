-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProductOn_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:48.498856+00:00
-- url     : https://prove2.me/theorems/71e52245-5d38-4461-ad18-afa3e6101c0f
-- title:
--   BPTCommuting Projector Model: projector Product On is Symmetric Projection
-- statement:
--   Grouped source products remain honest finite-dimensional orthogonal projectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2110-L2118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2110-L2118

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    (M.projectorProductOn checks).IsSymmetricProjection := by sorry
