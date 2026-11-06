-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_fixed_iff
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_fixed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:11.96723+00:00
-- url     : https://prove2.me/theorems/51aaa39e-9852-484f-a31d-4b2e801edf07
-- title:
--   BPTCommuting Projector Model: full Code Projector fixed iff
-- statement:
--   The constructed full projector fixes exactly the common-fixed code space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L284-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L284-L289

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_fixed_iff (M : BPTCommutingProjectorModel L κ)
    (vector : L.Register) :
    M.fullCodeProjector vector = vector ↔ ∀ check, M.projector check vector = vector := by sorry
