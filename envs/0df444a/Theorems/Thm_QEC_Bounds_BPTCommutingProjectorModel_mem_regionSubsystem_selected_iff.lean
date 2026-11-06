-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
-- name    : QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:34:24.245599+00:00
-- url     : https://prove2.me/theorems/36631dd6-b25a-4cdc-bec2-8c3944924f25
-- title:
--   BPTCommuting Projector Model: mem region Subsystem selected iff
-- statement:
--   The model-region bridge has the expected pointwise membership specification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L467-L470
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L467-L470

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

theorem QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) (site : L.Site) :
    site ∈ (M.regionSubsystem region).selected ↔ site ∈ region := by sorry
