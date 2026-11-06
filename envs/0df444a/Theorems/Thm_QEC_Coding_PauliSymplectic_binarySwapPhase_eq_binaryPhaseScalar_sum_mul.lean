-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_binaryPhaseScalar_sum_mul
-- name    : QEC.Coding.PauliSymplectic.binarySwapPhase_eq_binaryPhaseScalar_sum_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:19:17.444252+00:00
-- url     : https://prove2.me/theorems/be2f2df8-d7a1-4e48-8c96-71058903e24a
-- title:
--   Pauli Symplectic: binary Swap Phase eq binary Phase Scalar sum mul
-- statement:
--   The Pauli Symplectic construction uses the binary Swap Phase eq binary Phase Scalar sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L574-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L574-L582

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

theorem QEC.Coding.PauliSymplectic.binarySwapPhase_eq_binaryPhaseScalar_sum_mul (x z : Word (ZMod 2) ι) :
    binarySwapPhase x z =
      binaryPhaseScalar (Finset.sum Finset.univ fun i => x i * z i) := by sorry
