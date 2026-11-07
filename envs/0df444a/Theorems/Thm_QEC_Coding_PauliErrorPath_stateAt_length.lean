-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_length
-- name    : QEC.Coding.PauliErrorPath.stateAt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:39.896218+00:00
-- url     : https://prove2.me/theorems/1339795f-a3d9-4c3d-9931-61a6cc56d06f
-- title:
--   Pauli Error Path: state At length
-- statement:
--   The Pauli Error Path construction uses the state At length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L137-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L137-L139

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

theorem QEC.Coding.PauliErrorPath.stateAt_length (γ : PauliErrorPath (ι := ι)) :
    γ.stateAt γ.increments.length = γ.endpoint := by sorry
