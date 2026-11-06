-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_primaryBitBoundary_le_three
-- name    : QEC.Coding.ClassicalWeightReduction.HammingWeight_primaryBitBoundary_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:37.345073+00:00
-- url     : https://prove2.me/theorems/20f4937d-00d5-4c9e-902f-b645856a05f6
-- title:
--   Classical Weight Reduction: Hamming Weight primary Bit Boundary le three
-- statement:
--   Every primary bit participates in at most three weight-reduced checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L637-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L637-L657

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

theorem QEC.Coding.ClassicalWeightReduction.HammingWeight_primaryBitBoundary_le_three (e : Incidence R) :
    HammingWeight (primaryBitBoundary (F := F) R e) ≤ 3 := by sorry
