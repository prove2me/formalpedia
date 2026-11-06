-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_commute_projectorCD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorBC_commute_projectorCD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:58.186731+00:00
-- url     : https://prove2.me/theorems/f33dc7dd-55b6-4a43-b004-f5811957461b
-- title:
--   BPTCommuting Projector Model: projector BC commute projector CD
-- statement:
--   The three source grouped projectors commute pairwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2510-L2512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2510-L2512

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorBC_commute_projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Commute (M.projectorBC region) (M.projectorCD region) := by sorry
