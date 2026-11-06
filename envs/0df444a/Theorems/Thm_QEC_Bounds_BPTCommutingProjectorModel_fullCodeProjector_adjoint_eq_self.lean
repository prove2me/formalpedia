-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_adjoint_eq_self
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:01:08.356197+00:00
-- url     : https://prove2.me/theorems/f1911108-e613-4584-90c0-91e6de0c14f8
-- title:
--   BPTCommuting Projector Model: full Code Projector adjoint eq self
-- statement:
--   The full projector is self-adjoint because it is the code-space projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L297-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L297-L299

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_adjoint_eq_self (M : BPTCommutingProjectorModel L κ) :
    LinearMap.adjoint M.fullCodeProjector = M.fullCodeProjector := by sorry
