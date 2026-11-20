-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_fixed_scale_no_bounded_response
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.fixed_scale_no_bounded_response
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:31:11.441122+00:00
-- url     : https://prove2.me/theorems/a8853fd1-e25f-48bc-9c45-1eafaf3bd18a
-- title:
--   BDL26 Local Background Comparison Depth: fixed scale no bounded response
-- statement:
--   At a fixed scale, a real canonical-generator prefix forces response weight
--   larger than ANY proposed depth-independent finite budget. Both full comparison
--   correction calls remain in the residual and in the restriction comparator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L114-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L114-L159

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.fixed_scale_no_bounded_response (S : OddScale) (large : 33 ≤ S.ell) (B : Nat) :
    ∃ (P : Finset (Q S (budgetDepth B))) (q : Q S (budgetDepth B)),
      P ⊆ hammingSupport (logicalError S (budgetDepth B)) ∧
      q ∈ hammingSupport (logicalError S (budgetDepth B)) ∧ q ∉ P ∧
      let g := backgroundRestriction S (budgetDepth B) (logicalError S (budgetDepth B)) P
      B < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S (budgetDepth B)) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) ∧
      ∀ A : Finset (Q S (budgetDepth B)),
        HammingWeight (backgroundRestriction S (budgetDepth B) g A) ≤ B →
        BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
          (perturbTop S (budgetDepth B)
            (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
          (canonicalBasisWord (F:=BDL26Field) q)-
        BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
          (perturbTop S (budgetDepth B)
            (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B))
            (backgroundRestriction S (budgetDepth B) g A))
          (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) := by sorry
