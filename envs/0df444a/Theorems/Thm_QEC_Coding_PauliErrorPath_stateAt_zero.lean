-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_zero
-- name    : QEC.Coding.PauliErrorPath.stateAt_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:27.507085+00:00
-- url     : https://prove2.me/theorems/14dd5faf-25fc-415f-8dbd-d47d8b0208d5
-- title:
--   Pauli Error Path: state At zero
-- statement:
--   The Pauli Error Path construction uses the state At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L132-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L132-L134

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

theorem QEC.Coding.PauliErrorPath.stateAt_zero (γ : PauliErrorPath (ι := ι)) :
    γ.stateAt 0 = binaryOne := by sorry
