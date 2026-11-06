-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_combineInverseMap1_single
-- name    : QEC.Coding.ClassicalWeightReduction.transpose_combineInverseMap1_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:57:05.664901+00:00
-- url     : https://prove2.me/theorems/1a278109-c4c1-4022-979f-8345c2a19e7f
-- title:
--   Classical Weight Reduction: transpose combine Inverse Map1 single
-- statement:
--   The Classical Weight Reduction construction uses the transpose combine Inverse Map1 single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L154-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L154-L186

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

theorem QEC.Coding.ClassicalWeightReduction.transpose_combineInverseMap1_single
    (q : WeightReducedBit R) :
    wordLinearMapTranspose (combineInverseMap1 (F := F) R)
        (Pi.single q 1) =
      match q with
      | Sum.inl e => Pi.single (Sum.inl e.1.2) 1
      | Sum.inr a => Pi.single (Sum.inr a) 1 := by sorry
