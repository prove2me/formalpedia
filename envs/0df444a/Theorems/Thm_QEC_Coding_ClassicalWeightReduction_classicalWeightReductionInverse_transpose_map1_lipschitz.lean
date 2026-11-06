-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_classicalWeightReductionInverse_transpose_map1_lipschitz
-- name    : QEC.Coding.ClassicalWeightReduction.classicalWeightReductionInverse_transpose_map1_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:59.290024+00:00
-- url     : https://prove2.me/theorems/dd177697-9d97-4134-baf7-c1ca3dac6bc1
-- title:
--   Classical Weight Reduction: classical Weight Reduction Inverse transpose map1 lipschitz
-- statement:
--   If original check degree is at most `L`, the transpose of the complete
--   inverse map is `L`-Lipschitz.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L299-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L299-L309

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

theorem QEC.Coding.ClassicalWeightReduction.classicalWeightReductionInverse_transpose_map1_lipschitz
    [CharP F 2] (h : HasNoIsolatedVertices R) (L : Nat)
    (hDegree : ∀ c : Check, Fintype.card (CheckNeighbor R c) ≤ L)
    (x : Word F (WeightReducedBit R)) :
    HammingWeight
        (wordLinearMapTranspose
          (classicalWeightReductionInverseChainMap (F₀ := F) R h).map1 x) ≤
      L * HammingWeight x := by sorry
