-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_succ
-- name    : QEC.Coding.PauliErrorPath.stateAt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:19.789946+00:00
-- url     : https://prove2.me/theorems/cef314f9-b79c-4bd2-a4d1-51045cdcfd45
-- title:
--   Pauli Error Path: state At succ
-- statement:
--   Consecutive accumulated states differ by the stored increment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L169-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L169-L174

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

theorem QEC.Coding.PauliErrorPath.stateAt_succ (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.increments.length) :
    γ.stateAt (n + 1) =
      binaryMul (γ.stateAt n) γ.increments[n] := by sorry
