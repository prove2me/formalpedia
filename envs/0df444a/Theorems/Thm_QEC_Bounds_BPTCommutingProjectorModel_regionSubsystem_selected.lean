-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:34:16.263525+00:00
-- url     : https://prove2.me/theorems/e0d212f3-358d-445f-8cc1-8f6db76e8e13
-- title:
--   BPTCommuting Projector Model: region Subsystem selected
-- statement:
--   The model-region bridge preserves the exact selected site set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L461-L463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L461-L463

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

theorem QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : (M.regionSubsystem region).selected = region := by sorry
