-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_neg_one_pow_binaryOverlapCount
-- name    : QEC.Coding.PauliSymplectic.binarySwapPhase_eq_neg_one_pow_binaryOverlapCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:12:32.478331+00:00
-- url     : https://prove2.me/theorems/87e8e799-b2b9-4d1a-af2a-6a0709596f42
-- title:
--   Pauli Symplectic: binary Swap Phase eq neg one pow binary Overlap Count
-- statement:
--   The raw normal-order swap phase is exactly `(-1)` to the number of local
--   `Y` coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L58-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L58-L78

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.binarySwapPhase_eq_neg_one_pow_binaryOverlapCount (P : Binary ι) :
    binarySwapPhase P.vector.xPart P.vector.zPart =
      (-1 : Complex) ^ binaryOverlapCount P := by sorry
