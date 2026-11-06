-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_mem_scopedErrorOperators_iff
-- name    : QEC.Coding.PauliSymplectic.mem_scopedErrorOperators_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:20:18.218738+00:00
-- url     : https://prove2.me/theorems/6e5f478d-9490-42f4-b14c-0ec66ff70a36
-- title:
--   Pauli Symplectic: mem scoped Error Operators iff
-- statement:
--   The Pauli Symplectic construction uses the mem scoped Error Operators iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L738-L742
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L738-L742

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

theorem QEC.Coding.PauliSymplectic.mem_scopedErrorOperators_iff (B : Nat)
    (E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :
    E ∈ scopedErrorOperators (ι := ι) B ↔
      ∃ P : Binary ι, P ∈ scopedByWeight (ι := ι) B ∧ toQubitOperator P = E := by sorry
