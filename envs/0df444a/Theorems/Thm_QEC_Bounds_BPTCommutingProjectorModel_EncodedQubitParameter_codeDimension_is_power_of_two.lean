-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_EncodedQubitParameter_codeDimension_is_power_of_two
-- name    : QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.codeDimension_is_power_of_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:09:16.636751+00:00
-- url     : https://prove2.me/theorems/908033de-7911-4dae-8818-0629bc0691db
-- title:
--   Encoded Qubit Parameter: code Dimension is power of two
-- statement:
--   The encoded-qubit parameter explicitly witnesses a power-of-two code dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L388-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L388-L391

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

theorem QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.codeDimension_is_power_of_two
    {M : BPTCommutingProjectorModel L κ} (parameter : EncodedQubitParameter M) :
    ∃ k, M.codeSpace.dimension = 2 ^ k := by sorry
