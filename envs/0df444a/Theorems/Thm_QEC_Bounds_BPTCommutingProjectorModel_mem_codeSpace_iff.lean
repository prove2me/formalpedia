-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_codeSpace_iff
-- name    : QEC.Bounds.BPTCommutingProjectorModel.mem_codeSpace_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:09:30.404839+00:00
-- url     : https://prove2.me/theorems/d2771a21-9e40-48c0-acc0-fb2184db67f3
-- title:
--   BPTCommuting Projector Model: mem code Space iff
-- statement:
--   Exact membership specification for the common-fixed code space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L274-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L274-L276

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

theorem QEC.Bounds.BPTCommutingProjectorModel.mem_codeSpace_iff (M : BPTCommutingProjectorModel L κ) (vector : L.Register) :
    vector ∈ M.codeSpace.carrier ↔ ∀ check, M.projector check vector = vector := by sorry
