-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndromeBit_eq_one_iff_not_commutes
-- name    : QEC.Coding.PauliSymplectic.stabilizerSyndromeBit_eq_one_iff_not_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:46.580696+00:00
-- url     : https://prove2.me/theorems/18f10c0b-3634-4c42-9389-9150b16d540f
-- title:
--   Pauli Symplectic: stabilizer Syndrome Bit eq one iff not commutes
-- statement:
--   A syndrome bit is one exactly for anticommuting binary Paulis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1581-L1591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1581-L1591

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

theorem QEC.Coding.PauliSymplectic.stabilizerSyndromeBit_eq_one_iff_not_commutes (M E : Binary ι) :
    stabilizerSyndromeBit M E = 1 ↔ ¬ Commutes E M := by sorry
