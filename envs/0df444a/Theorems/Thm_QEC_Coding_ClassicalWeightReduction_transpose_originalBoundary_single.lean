-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_originalBoundary_single
-- name    : QEC.Coding.ClassicalWeightReduction.transpose_originalBoundary_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:40:19.250661+00:00
-- url     : https://prove2.me/theorems/9315ac21-6bc3-4983-b495-4ab4c58cd33a
-- title:
--   Classical Weight Reduction: transpose original Boundary single
-- statement:
--   A row of the transposed original Tanner boundary is its incidence word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L513-L518
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L513-L518

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [DecidableEq F]

theorem QEC.Coding.ClassicalWeightReduction.transpose_originalBoundary_single (c : Check) :
    wordLinearMapTranspose (originalBoundary (F := F) R) (Pi.single c 1) =
      fun b => if R c b then 1 else 0 := by sorry
