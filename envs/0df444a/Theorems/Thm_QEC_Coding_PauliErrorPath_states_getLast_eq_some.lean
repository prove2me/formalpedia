-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_states_getLast_eq_some
-- name    : QEC.Coding.PauliErrorPath.states_getLast_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:45.776945+00:00
-- url     : https://prove2.me/theorems/78b433e8-9e10-4721-852b-441032948b41
-- title:
--   Pauli Error Path: states get Last eq some
-- statement:
--   The Pauli Error Path construction uses the states get Last eq some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L152-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L152-L154

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

theorem QEC.Coding.PauliErrorPath.states_getLast_eq_some (γ : PauliErrorPath (ι := ι)) :
    γ.states.getLast? = some γ.endpoint := by sorry
