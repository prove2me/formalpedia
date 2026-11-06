-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_collapseInverseMap1_single_auxiliary_weight_le
-- name    : QEC.Coding.ClassicalWeightReduction.transpose_collapseInverseMap1_single_auxiliary_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:55:53.741538+00:00
-- url     : https://prove2.me/theorems/7944ea61-38cd-4119-b826-26fcd79d513d
-- title:
--   Classical Weight Reduction: transpose collapse Inverse Map1 single auxiliary weight le
-- statement:
--   The Classical Weight Reduction construction uses the transpose collapse Inverse Map1 single auxiliary weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L244-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L244-L271

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

theorem QEC.Coding.ClassicalWeightReduction.transpose_collapseInverseMap1_single_auxiliary_weight_le
    (a : AuxiliaryBit R) (L : Nat)
    (hDegree : Fintype.card (CheckNeighbor R a.1) ≤ L) :
    HammingWeight
        (wordLinearMapTranspose (collapseInverseMap1 (F := F) R)
          (Pi.single (Sum.inr a) 1)) ≤ L := by sorry
