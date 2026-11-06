-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorCD_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorCD_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:38.591605+00:00
-- url     : https://prove2.me/theorems/4850475d-5e1e-412c-827f-bb2b18948d41
-- title:
--   BPTCommuting Projector Model: projector CD is Symmetric Projection
-- statement:
--   Each source grouped product is an actual orthogonal projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2495-L2497
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2495-L2497

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorCD_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.projectorCD region).IsSymmetricProjection := by sorry
