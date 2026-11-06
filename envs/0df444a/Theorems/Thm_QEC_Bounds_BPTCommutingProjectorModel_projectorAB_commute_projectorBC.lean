-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_commute_projectorBC
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorBC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:19.009317+00:00
-- url     : https://prove2.me/theorems/3e8f2842-6a25-4e77-8657-d7111d33422b
-- title:
--   BPTCommuting Projector Model: projector AB commute projector BC
-- statement:
--   The three source grouped projectors commute pairwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2500-L2502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2500-L2502

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorBC (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : Commute (M.projectorAB region) (M.projectorBC region) := by sorry
