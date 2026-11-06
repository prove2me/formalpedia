-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_projectorCDLocal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorCDLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:19.175105+00:00
-- url     : https://prove2.me/theorems/fc2a8c59-8f6f-4ad8-9078-7c4997fd353c
-- title:
--   BPTCommuting Projector Model: extend Local To Register projector CDLocal
-- statement:
--   The chosen `CD` representative extends back to the actual source product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2323-L2327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2323-L2327

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

theorem QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorCDLocal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).extendLocalToRegister (M.projectorCDLocal region) =
      M.projectorCD region := by sorry
