-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_states_length
-- name    : QEC.Coding.PauliErrorPath.states_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:57.835881+00:00
-- url     : https://prove2.me/theorems/0feb61f8-19ea-4ef1-aaaa-ac0d8f4171dd
-- title:
--   Pauli Error Path: states length
-- statement:
--   The Pauli Error Path construction uses the states length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L142-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L142-L144

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.PauliErrorPath

theorem QEC.Coding.PauliErrorPath.states_length (γ : PauliErrorPath (ι := ι)) :
    γ.states.length = γ.increments.length + 1 := by sorry
