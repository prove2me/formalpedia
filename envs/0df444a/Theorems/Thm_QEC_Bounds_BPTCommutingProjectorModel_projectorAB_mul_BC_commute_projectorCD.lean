-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_mul_BC_commute_projectorCD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_commute_projectorCD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:08.927672+00:00
-- url     : https://prove2.me/theorems/a7c94cc0-0c77-4347-887b-b60c008de01d
-- title:
--   BPTCommuting Projector Model: projector AB mul BC commute projector CD
-- statement:
--   The `MC` and `CD` source projectors commute across the first BV03 cut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2621-L2637
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2621-L2637

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_commute_projectorCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute (M.projectorAB region * M.projectorBC region) (M.projectorCD region) := by sorry
