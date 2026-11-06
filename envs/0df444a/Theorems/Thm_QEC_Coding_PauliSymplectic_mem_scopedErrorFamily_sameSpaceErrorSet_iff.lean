-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_mem_scopedErrorFamily_sameSpaceErrorSet_iff
-- name    : QEC.Coding.PauliSymplectic.mem_scopedErrorFamily_sameSpaceErrorSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:25:32.217742+00:00
-- url     : https://prove2.me/theorems/fa600099-2581-4931-a27d-ff598d6a803e
-- title:
--   Pauli Symplectic: mem scoped Error Family same Space Error Set iff
-- statement:
--   The Pauli Symplectic construction uses the mem scoped Error Family same Space Error Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L763-L767
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L763-L767

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

theorem QEC.Coding.PauliSymplectic.mem_scopedErrorFamily_sameSpaceErrorSet_iff (B : Nat)
    (E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :
    E ∈ (scopedErrorFamily (ι := ι) B).sameSpaceErrorSet ↔
      E ∈ scopedErrorOperators (ι := ι) B := by sorry
