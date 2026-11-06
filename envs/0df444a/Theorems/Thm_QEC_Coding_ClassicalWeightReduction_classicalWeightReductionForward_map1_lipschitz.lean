-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_classicalWeightReductionForward_map1_lipschitz
-- name    : QEC.Coding.ClassicalWeightReduction.classicalWeightReductionForward_map1_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:50.384415+00:00
-- url     : https://prove2.me/theorems/097c3509-9393-498e-a42a-634227180dfc
-- title:
--   Classical Weight Reduction: classical Weight Reduction Forward map1 lipschitz
-- statement:
--   The complete forward map of classical weight reduction does not increase
--   Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L142-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L142-L151

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

theorem QEC.Coding.ClassicalWeightReduction.classicalWeightReductionForward_map1_lipschitz
    [CharP F 2] (h : HasNoIsolatedVertices R)
    (x : Word F (WeightReducedBit R)) :
    HammingWeight
        ((classicalWeightReductionForwardChainMap (F₀ := F) R h).map1 x) ≤
      HammingWeight x := by sorry
