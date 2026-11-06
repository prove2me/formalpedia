-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:20.172196+00:00
-- url     : https://prove2.me/theorems/6c3fa6f5-452e-4bc0-bc97-5ce6b05c3880
-- title:
--   BPTCommuting Projector Model: projector AB is Symmetric Projection
-- statement:
--   Each source grouped product is an actual orthogonal projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2485-L2487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2485-L2487

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.projectorAB region).IsSymmetricProjection := by sorry
