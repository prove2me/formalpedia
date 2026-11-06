-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorBC_isSymmetricProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:48.518193+00:00
-- url     : https://prove2.me/theorems/c32a403b-94c8-4dcc-a58a-b4d0bbacefd7
-- title:
--   BPTCommuting Projector Model: projector BC is Symmetric Projection
-- statement:
--   Each source grouped product is an actual orthogonal projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2490-L2492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2490-L2492

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorBC_isSymmetricProjection (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.projectorBC region).IsSymmetricProjection := by sorry
