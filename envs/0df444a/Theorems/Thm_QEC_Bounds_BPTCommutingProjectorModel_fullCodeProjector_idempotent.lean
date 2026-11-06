-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_idempotent
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:00:46.938742+00:00
-- url     : https://prove2.me/theorems/f45268d6-0556-474e-9024-9686a16f8486
-- title:
--   BPTCommuting Projector Model: full Code Projector idempotent
-- statement:
--   The full projector is idempotent because it is the code-space projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L292-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L292-L294

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_idempotent (M : BPTCommutingProjectorModel L κ) :
    M.fullCodeProjector.comp M.fullCodeProjector = M.fullCodeProjector := by sorry
