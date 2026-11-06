-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureChannel_specification
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionErasureChannel_specification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:09:26.80921+00:00
-- url     : https://prove2.me/theorems/de0bb2fc-ca5a-45f9-a853-6c7d72851da7
-- title:
--   BPTCommuting Projector Model: region Erasure Channel specification
-- statement:
--   The model-region erasure channel is exactly the selected subsystem channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L479-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L479-L482

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

theorem QEC.Bounds.BPTCommutingProjectorModel.regionErasureChannel_specification (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) :
    M.regionErasureChannel region = (M.regionSubsystem region).erasureChannelFromRegister := by sorry
