-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryUpToSign_iff_exists_binarySign
-- name    : QEC.Coding.PauliSymplectic.binaryUpToSign_iff_exists_binarySign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:39.537189+00:00
-- url     : https://prove2.me/theorems/412cf8d4-31ff-4766-9d9f-ba02112783b7
-- title:
--   Pauli Symplectic: binary Up To Sign iff exists binary Sign
-- statement:
--   `BinaryUpToSign` is precisely multiplication by one of the two global signs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1481-L1492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1481-L1492

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

theorem QEC.Coding.PauliSymplectic.binaryUpToSign_iff_exists_binarySign (P Q : Binary ι) :
    BinaryUpToSign P Q ↔ ∃ phase : ZMod 2, P = binaryMul (binarySign phase) Q := by sorry
