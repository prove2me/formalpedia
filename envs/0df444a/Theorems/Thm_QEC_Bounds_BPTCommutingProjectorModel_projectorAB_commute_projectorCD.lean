-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_commute_projectorCD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorCD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:50.21336+00:00
-- url     : https://prove2.me/theorems/c2fa396d-d118-46c9-bda3-bd5d9a00018f
-- title:
--   BPTCommuting Projector Model: projector AB commute projector CD
-- statement:
--   The three source grouped projectors commute pairwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2505-L2507
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2505-L2507

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Commute (M.projectorAB region) (M.projectorCD region) := by sorry
