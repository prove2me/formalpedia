-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_collapseInverseMap1_single_original
-- name    : QEC.Coding.ClassicalWeightReduction.transpose_collapseInverseMap1_single_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:42.501909+00:00
-- url     : https://prove2.me/theorems/8d181f68-a7b7-4215-8ecc-7d32d4b7d447
-- title:
--   Classical Weight Reduction: transpose collapse Inverse Map1 single original
-- statement:
--   The Classical Weight Reduction construction uses the transpose collapse Inverse Map1 single original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L202-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L202-L215

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
open QEC.Coding.ClassicalWeightReduction
variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [DecidableEq F]

theorem QEC.Coding.ClassicalWeightReduction.transpose_collapseInverseMap1_single_original (b : Bit) :
    wordLinearMapTranspose (collapseInverseMap1 (F := F) R)
        (Pi.single (Sum.inl b) 1) =
      Pi.single b 1 := by sorry
