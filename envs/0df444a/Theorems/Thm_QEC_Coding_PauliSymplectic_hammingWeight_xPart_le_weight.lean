-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_xPart_le_weight
-- name    : QEC.Coding.PauliSymplectic.hammingWeight_xPart_le_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:21:43.082894+00:00
-- url     : https://prove2.me/theorems/2fcd58e4-a14d-4a5c-93e4-d83eb7b58e53
-- title:
--   Pauli Symplectic: hamming Weight x Part le weight
-- statement:
--   The `X` coordinate Hamming weight is bounded by total binary Pauli weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L444-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L444-L453

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

theorem QEC.Coding.PauliSymplectic.hammingWeight_xPart_le_weight (P : Binary ι) :
    HammingWeight P.vector.xPart ≤ weight P := by sorry
