-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryDagger_right
-- name    : QEC.Coding.PauliSymplectic.commutes_binaryDagger_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:31.772366+00:00
-- url     : https://prove2.me/theorems/1b836e8d-d410-4f13-9982-9d9d61d176b6
-- title:
--   Pauli Symplectic: commutes binary Dagger right
-- statement:
--   Commutation is unchanged by replacing a binary Pauli by its dagger.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1422-L1424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1422-L1424

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

theorem QEC.Coding.PauliSymplectic.commutes_binaryDagger_right {E P : Binary ι} (hP : Commutes E P) :
    Commutes E (binaryDagger P) := by sorry
