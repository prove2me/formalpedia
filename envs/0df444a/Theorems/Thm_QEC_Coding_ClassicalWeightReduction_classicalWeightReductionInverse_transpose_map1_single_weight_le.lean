-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_classicalWeightReductionInverse_transpose_map1_single_weight_le
-- name    : QEC.Coding.ClassicalWeightReduction.classicalWeightReductionInverse_transpose_map1_single_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:38.946926+00:00
-- url     : https://prove2.me/theorems/ce57ad2f-97ae-4456-9a5b-b3b9e47ae434
-- title:
--   Classical Weight Reduction: classical Weight Reduction Inverse transpose map1 single weight le
-- statement:
--   The Classical Weight Reduction construction uses the classical Weight Reduction Inverse transpose map1 single weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L273-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L273-L295

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

theorem QEC.Coding.ClassicalWeightReduction.classicalWeightReductionInverse_transpose_map1_single_weight_le
    [CharP F 2] (h : HasNoIsolatedVertices R) (L : Nat)
    (hDegree : ∀ c : Check, Fintype.card (CheckNeighbor R c) ≤ L)
    (q : WeightReducedBit R) :
    HammingWeight
        (wordLinearMapTranspose
          (classicalWeightReductionInverseChainMap (F₀ := F) R h).map1
          (Pi.single q 1)) ≤ L := by sorry
