-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_of_symplecticForm_eq_zero
-- name    : QEC.Coding.PauliSymplectic.binarySwapPhase_eq_of_symplecticForm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:48.855702+00:00
-- url     : https://prove2.me/theorems/71334cf6-7445-48ac-ab34-317b4290d64e
-- title:
--   Pauli Symplectic: binary Swap Phase eq of symplectic Form eq zero
-- statement:
--   The Pauli Symplectic construction uses the binary Swap Phase eq of symplectic Form eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1047-L1066
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1047-L1066

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

theorem QEC.Coding.PauliSymplectic.binarySwapPhase_eq_of_symplecticForm_eq_zero (P Q : Binary ι)
    (h : symplecticForm P.vector Q.vector = 0) :
    binarySwapPhase Q.vector.xPart P.vector.zPart =
      binarySwapPhase P.vector.xPart Q.vector.zPart := by sorry
