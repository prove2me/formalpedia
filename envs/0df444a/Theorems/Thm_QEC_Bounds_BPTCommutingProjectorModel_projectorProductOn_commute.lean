-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProductOn_commute
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:20.707051+00:00
-- url     : https://prove2.me/theorems/92da1c93-abfb-46e4-81e3-81c2f4e7b8e1
-- title:
--   BPTCommuting Projector Model: projector Product On commute
-- statement:
--   Products of any two selected BPT check families commute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2121-L2133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2121-L2133

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_commute (M : BPTCommutingProjectorModel L kappa)
    (left right : Finset kappa) :
    Commute (M.projectorProductOn left) (M.projectorProductOn right) := by sorry
