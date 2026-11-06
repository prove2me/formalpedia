-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_EncodedQubitParameter_encodedQubits_eq_log2
-- name    : QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.encodedQubits_eq_log2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:09:06.333305+00:00
-- url     : https://prove2.me/theorems/510fb2b1-5e2f-41ac-b89f-35f19fe5d1ce
-- title:
--   Encoded Qubit Parameter: encoded Qubits eq log2
-- statement:
--   The code-dimension witness supplies the source convention `k = log2(dim C)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L381-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L381-L385

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

theorem QEC.Bounds.BPTCommutingProjectorModel.EncodedQubitParameter.encodedQubits_eq_log2
    {M : BPTCommutingProjectorModel L κ} (parameter : EncodedQubitParameter M) :
    Nat.log 2 M.codeSpace.dimension = parameter.encodedQubits := by sorry
