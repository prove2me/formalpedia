-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_neg_of_not_commutes
-- name    : QEC.Coding.PauliSymplectic.binarySwapPhase_eq_neg_of_not_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:26.73322+00:00
-- url     : https://prove2.me/theorems/71c4b036-14dd-4231-bdb4-b0e562829a48
-- title:
--   Pauli Symplectic: binary Swap Phase eq neg of not commutes
-- statement:
--   The Pauli Symplectic construction uses the binary Swap Phase eq neg of not commutes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1119-L1136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1119-L1136

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

theorem QEC.Coding.PauliSymplectic.binarySwapPhase_eq_neg_of_not_commutes (P Q : Binary ι)
    (h : ¬ Commutes P Q) :
    binarySwapPhase Q.vector.xPart P.vector.zPart =
      -binarySwapPhase P.vector.xPart Q.vector.zPart := by sorry
