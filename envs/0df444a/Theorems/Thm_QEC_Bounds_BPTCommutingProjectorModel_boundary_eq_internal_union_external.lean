-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_eq_internal_union_external
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundary_eq_internal_union_external
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:36:01.37656+00:00
-- url     : https://prove2.me/theorems/7765c214-c5fe-4d93-9c37-e817dd37452f
-- title:
--   BPTCommuting Projector Model: boundary eq internal union external
-- statement:
--   The source boundary splits into its internal and external portions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L447-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L447-L452

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundary_eq_internal_union_external (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) :
    M.boundary region = M.internalBoundary region ∪ M.externalBoundary region := by sorry
