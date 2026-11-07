-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_take
-- name    : QEC.Coding.PauliErrorPath.endpoint_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:56.7603+00:00
-- url     : https://prove2.me/theorems/8c204dcb-852a-42b0-b332-4854c7995adc
-- title:
--   Pauli Error Path: endpoint take
-- statement:
--   The Pauli Error Path construction uses the endpoint take property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L182-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L182-L184

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

theorem QEC.Coding.PauliErrorPath.endpoint_take (γ : PauliErrorPath (ι := ι)) (n : Nat) :
    (γ.take n).endpoint = γ.stateAt n := by sorry

attribute [defeq] QEC.Coding.PauliErrorPath.endpoint_take
