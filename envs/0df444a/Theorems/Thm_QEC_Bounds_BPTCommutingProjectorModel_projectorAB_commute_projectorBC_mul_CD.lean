-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_commute_projectorBC_mul_CD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorBC_mul_CD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:30.283271+00:00
-- url     : https://prove2.me/theorems/cdcb1938-5957-4a4e-8e9f-18be7d1beadf
-- title:
--   BPTCommuting Projector Model: projector AB commute projector BC mul CD
-- statement:
--   The `AB` and `B bar(M)` source projectors commute across the second BV03 cut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2640-L2656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2640-L2656

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorBC_mul_CD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute (M.projectorAB region) (M.projectorBC region * M.projectorCD region) := by sorry
