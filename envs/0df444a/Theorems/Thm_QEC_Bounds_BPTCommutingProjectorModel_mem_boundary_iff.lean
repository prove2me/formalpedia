-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_boundary_iff
-- name    : QEC.Bounds.BPTCommutingProjectorModel.mem_boundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:10:20.537539+00:00
-- url     : https://prove2.me/theorems/c6d74727-58c1-448c-a20b-874ab4d6cac4
-- title:
--   BPTCommuting Projector Model: mem boundary iff
-- statement:
--   Membership in the source boundary has an exact support-coupling witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L414-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L414-L418

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

theorem QEC.Bounds.BPTCommutingProjectorModel.mem_boundary_iff (M : BPTCommutingProjectorModel L κ) (region : Finset L.Site)
    (site : L.Site) :
    site ∈ M.boundary region ↔
      ∃ check, M.supportCouples check region ∧ site ∈ M.support check := by sorry
