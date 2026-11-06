-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_iff_of_binaryUpToSign_left
-- name    : QEC.Coding.PauliSymplectic.commutes_iff_of_binaryUpToSign_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:26:37.278889+00:00
-- url     : https://prove2.me/theorems/00402810-0f95-45c0-95ef-9f726d6c2758
-- title:
--   Pauli Symplectic: commutes iff of binary Up To Sign left
-- statement:
--   Commutation is invariant under the binary global-sign quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1508-L1512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1508-L1512

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.commutes_iff_of_binaryUpToSign_left {P Q R : Binary ι}
    (h : BinaryUpToSign P Q) : Commutes P R ↔ Commutes Q R := by sorry
