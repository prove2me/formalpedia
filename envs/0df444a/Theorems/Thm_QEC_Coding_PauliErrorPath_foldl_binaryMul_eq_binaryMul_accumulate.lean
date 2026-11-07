-- Prove2me | Theorems.Thm_QEC_Coding_PauliErrorPath_foldl_binaryMul_eq_binaryMul_accumulate
-- name    : QEC.Coding.PauliErrorPath.foldl_binaryMul_eq_binaryMul_accumulate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:01.738093+00:00
-- url     : https://prove2.me/theorems/4192b504-a6fd-4e30-a431-3f77da70baf1
-- title:
--   Pauli Error Path: foldl binary Mul eq binary Mul accumulate
-- statement:
--   Starting a fold at `start` left-multiplies the identity-based accumulation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L101-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/ErrorPath.lean#L101-L111

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

theorem QEC.Coding.PauliErrorPath.foldl_binaryMul_eq_binaryMul_accumulate
    (steps : List (Binary ι)) (start : Binary ι) :
    steps.foldl binaryMul start = binaryMul start (accumulate steps) := by sorry
