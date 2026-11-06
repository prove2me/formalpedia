-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_weight_mul_le
-- name    : QEC.Coding.PauliSymplectic.weight_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:25:00.624486+00:00
-- url     : https://prove2.me/theorems/1d04a9d3-75e6-471b-8bb6-bfff2e4924f2
-- title:
--   Pauli Symplectic: weight mul le
-- statement:
--   The Pauli Symplectic construction uses the weight mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L682-L684
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L682-L684

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

theorem QEC.Coding.PauliSymplectic.weight_mul_le (P Q : Binary ι) :
    weight (binaryMul P Q) ≤ weight P + weight Q := by sorry
