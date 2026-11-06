-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_eq_projectorAB_mul_BC_mul_CD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_eq_projectorAB_mul_BC_mul_CD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:23.536013+00:00
-- url     : https://prove2.me/theorems/a81890c8-2519-4e9c-b9d1-d34101ae48bb
-- title:
--   BPTCommuting Projector Model: full Code Projector eq projector AB mul BC mul CD
-- statement:
--   The actual code projector is exactly the source `Pi_AB Pi_BC Pi_CD` product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2659-L2665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2659-L2665

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_eq_projectorAB_mul_BC_mul_CD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fullCodeProjector =
      (M.projectorAB region * M.projectorBC region) * M.projectorCD region := by sorry
