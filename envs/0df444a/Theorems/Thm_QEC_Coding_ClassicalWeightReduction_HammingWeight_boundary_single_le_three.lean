-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_boundary_single_le_three
-- name    : QEC.Coding.ClassicalWeightReduction.HammingWeight_boundary_single_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:32.932504+00:00
-- url     : https://prove2.me/theorems/ba9f8cf9-589f-46bf-b2e1-367ba0a95772
-- title:
--   Classical Weight Reduction: Hamming Weight boundary single le three
-- statement:
--   Every weight-reduced bit participates in at most three checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L723-L730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L723-L730

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
omit [Fintype F]

theorem QEC.Coding.ClassicalWeightReduction.HammingWeight_boundary_single_le_three (i : WeightReducedBit R) :
    HammingWeight (boundary (F := F) R (Pi.single i 1)) ≤ 3 := by sorry
