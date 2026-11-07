-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_append
-- name    : QEC.Coding.PauliErrorPath.endpoint_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:52:41.670199+00:00
-- url     : https://prove2.me/theorems/1dbeb043-cef6-4c76-8804-26478afdb83f
-- title:
--   Pauli Error Path: endpoint append
-- statement:
--   The endpoint of concatenated increments is the product of the endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L192-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L192-L194

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

theorem QEC.Coding.PauliErrorPath.endpoint_append (γ δ : PauliErrorPath (ι := ι)) :
    (γ.append δ).endpoint = binaryMul γ.endpoint δ.endpoint := by sorry
