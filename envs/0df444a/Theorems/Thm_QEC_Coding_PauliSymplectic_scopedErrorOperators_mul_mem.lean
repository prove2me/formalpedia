-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_scopedErrorOperators_mul_mem
-- name    : QEC.Coding.PauliSymplectic.scopedErrorOperators_mul_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:26:15.243044+00:00
-- url     : https://prove2.me/theorems/f2fc4980-0c4e-44ba-8387-c2028693a74b
-- title:
--   Pauli Symplectic: scoped Error Operators mul mem
-- statement:
--   The Pauli Symplectic construction uses the scoped Error Operators mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1029-L1037
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1029-L1037

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

theorem QEC.Coding.PauliSymplectic.scopedErrorOperators_mul_mem {B C : Nat}
    {E F : Semantics.Operator (Semantics.Qubit.QubitRegister ι)}
    (hE : E ∈ scopedErrorOperators (ι := ι) B)
    (hF : F ∈ scopedErrorOperators (ι := ι) C) :
    E * F ∈ scopedErrorOperators (ι := ι) (B + C) := by sorry
