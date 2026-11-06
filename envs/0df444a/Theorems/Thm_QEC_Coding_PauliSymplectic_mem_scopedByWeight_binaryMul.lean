-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_mem_scopedByWeight_binaryMul
-- name    : QEC.Coding.PauliSymplectic.mem_scopedByWeight_binaryMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:14.104961+00:00
-- url     : https://prove2.me/theorems/14d093c8-9993-419d-99ea-1ee942b2d174
-- title:
--   Pauli Symplectic: mem scoped By Weight binary Mul
-- statement:
--   The Pauli Symplectic construction uses the mem scoped By Weight binary Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L702-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L702-L707

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

theorem QEC.Coding.PauliSymplectic.mem_scopedByWeight_binaryMul {B C : Nat} {P Q : Binary ι}
    (hP : P ∈ scopedByWeight (ι := ι) B)
    (hQ : Q ∈ scopedByWeight (ι := ι) C) :
    binaryMul P Q ∈ scopedByWeight (ι := ι) (B + C) := by sorry
