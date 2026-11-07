-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_append
-- name    : QEC.Coding.PauliErrorPath.accumulate_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:37.564712+00:00
-- url     : https://prove2.me/theorems/09d9ef81-c7b2-428f-8d8d-cbdec83d1254
-- title:
--   Pauli Error Path: accumulate append
-- statement:
--   Accumulation respects list concatenation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L115-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L115-L119

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
omit [DecidableEq ι]

theorem QEC.Coding.PauliErrorPath.accumulate_append (left right : List (Binary ι)) :
    accumulate (left ++ right) =
      binaryMul (accumulate left) (accumulate right) := by sorry
