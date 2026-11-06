-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_auxiliaryCheckCoboundary_le_two
-- name    : QEC.Coding.ClassicalWeightReduction.HammingWeight_auxiliaryCheckCoboundary_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:28.500355+00:00
-- url     : https://prove2.me/theorems/f7734842-cf15-46d7-b38e-be3b75e0fb0a
-- title:
--   Classical Weight Reduction: Hamming Weight auxiliary Check Coboundary le two
-- statement:
--   Every auxiliary check acts on at most two weight-reduced bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L695-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L695-L701

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

theorem QEC.Coding.ClassicalWeightReduction.HammingWeight_auxiliaryCheckCoboundary_le_two (a : AuxiliaryCheck R) :
    HammingWeight (auxiliaryCheckCoboundary (F := F) R a) ≤ 2 := by sorry
