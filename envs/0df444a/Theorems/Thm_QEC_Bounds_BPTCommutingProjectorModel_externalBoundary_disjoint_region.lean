-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_disjoint_region
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_disjoint_region
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:07.803194+00:00
-- url     : https://prove2.me/theorems/77c9e76e-c3e5-4e87-b014-6d3bebabb8c3
-- title:
--   BPTCommuting Projector Model: external Boundary disjoint region
-- statement:
--   The external boundary lies in the complement of the region by construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L440-L444
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L440-L444

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

theorem QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_disjoint_region (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Disjoint (M.externalBoundary region) region := by sorry
