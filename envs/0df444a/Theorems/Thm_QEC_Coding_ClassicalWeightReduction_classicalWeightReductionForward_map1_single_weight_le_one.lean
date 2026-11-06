-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_classicalWeightReductionForward_map1_single_weight_le_one
-- name    : QEC.Coding.ClassicalWeightReduction.classicalWeightReductionForward_map1_single_weight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:50.421181+00:00
-- url     : https://prove2.me/theorems/8fcc59e2-2fc3-41f0-8094-0b4b738e5e9d
-- title:
--   Classical Weight Reduction: classical Weight Reduction Forward map1 single weight le one
-- statement:
--   The Classical Weight Reduction construction uses the classical Weight Reduction Forward map1 single weight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L109-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L109-L137

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
omit [Fintype F]

theorem QEC.Coding.ClassicalWeightReduction.classicalWeightReductionForward_map1_single_weight_le_one
    [CharP F 2] (h : HasNoIsolatedVertices R)
    (q : WeightReducedBit R) :
    HammingWeight
        ((classicalWeightReductionForwardChainMap (F₀ := F) R h).map1
          (Pi.single q 1)) ≤ 1 := by sorry
