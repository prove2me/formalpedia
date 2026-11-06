-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_externalBoundary_iff
-- name    : QEC.Bounds.BPTCommutingProjectorModel.mem_externalBoundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:11:00.632029+00:00
-- url     : https://prove2.me/theorems/f759cd09-8a0c-4483-917d-6c88ca2233d1
-- title:
--   BPTCommuting Projector Model: mem external Boundary iff
-- statement:
--   Membership in the external boundary is a complement-side support-coupling witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L428-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L428-L437

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

theorem QEC.Bounds.BPTCommutingProjectorModel.mem_externalBoundary_iff (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) (site : L.Site) :
    site ∈ M.externalBoundary region ↔
      site ∉ region ∧ ∃ check, M.supportCouples check region ∧ site ∈ M.support check := by sorry
