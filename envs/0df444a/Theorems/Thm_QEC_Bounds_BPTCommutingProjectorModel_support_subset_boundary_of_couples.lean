-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_support_subset_boundary_of_couples
-- name    : QEC.Bounds.BPTCommutingProjectorModel.support_subset_boundary_of_couples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:24.345457+00:00
-- url     : https://prove2.me/theorems/f95bea2e-d874-4237-9039-1b8c4dca88ab
-- title:
--   BPTCommuting Projector Model: support subset boundary of couples
-- statement:
--   Every coupled support is contained in the source boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L421-L425
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L421-L425

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]

theorem QEC.Bounds.BPTCommutingProjectorModel.support_subset_boundary_of_couples (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) (check : κ) (hcouples : M.supportCouples check region) :
    M.support check ⊆ M.boundary region := by sorry
