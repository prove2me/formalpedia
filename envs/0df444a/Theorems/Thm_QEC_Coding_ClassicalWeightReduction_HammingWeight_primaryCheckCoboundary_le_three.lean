-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_primaryCheckCoboundary_le_three
-- name    : QEC.Coding.ClassicalWeightReduction.HammingWeight_primaryCheckCoboundary_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:36.450317+00:00
-- url     : https://prove2.me/theorems/6d0bacf8-57fa-49c0-8bc9-4f827a4e0dad
-- title:
--   Classical Weight Reduction: Hamming Weight primary Check Coboundary le three
-- statement:
--   Every primary check acts on at most three weight-reduced bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L671-L691
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L671-L691

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

theorem QEC.Coding.ClassicalWeightReduction.HammingWeight_primaryCheckCoboundary_le_three (e : Incidence R) :
    HammingWeight (primaryCheckCoboundary (F := F) R e) ≤ 3 := by sorry
