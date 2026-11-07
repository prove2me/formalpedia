-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_states_getElem
-- name    : QEC.Coding.PauliErrorPath.states_getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:51:25.430463+00:00
-- url     : https://prove2.me/theorems/d34ca2cc-b504-41a9-8f9b-6b2ae0044c35
-- title:
--   Pauli Error Path: states get Elem
-- statement:
--   Every indexed accumulated state is the product of the corresponding prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L157-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L157-L160

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

theorem QEC.Coding.PauliErrorPath.states_getElem (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.states.length) :
    γ.states[n] = γ.stateAt n := by sorry
