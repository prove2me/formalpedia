-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_transpose_boundary_single_le_three
-- name    : QEC.Coding.ClassicalWeightReduction.HammingWeight_transpose_boundary_single_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:10.844793+00:00
-- url     : https://prove2.me/theorems/08d389eb-66b3-4265-8802-30e70509b8d0
-- title:
--   Classical Weight Reduction: Hamming Weight transpose boundary single le three
-- statement:
--   Every row of the actual transposed boundary has weight at most three.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L714-L719
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L714-L719

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

theorem QEC.Coding.ClassicalWeightReduction.HammingWeight_transpose_boundary_single_le_three
    (q : WeightReducedCheck R) :
    HammingWeight
      (wordLinearMapTranspose (boundary (F := F) R) (Pi.single q 1)) ≤ 3 := by sorry
