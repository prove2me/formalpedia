-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_bounded_selector_fails
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.bounded_selector_fails
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:29:00.350108+00:00
-- url     : https://prove2.me/theorems/32db39ae-e280-4ac7-8a6e-cdb713c8a962
-- title:
--   BDL26 Local Background Comparison Depth: bounded selector fails
-- statement:
--   Every adaptive selector of uniformly bounded coordinate sets fails, including
--   selectors depending on the whole background and on the actual flipped coordinate.
--   No graph or geometric radius assumption supplies the conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L177-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L177-L201

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.bounded_selector_fails (S : OddScale) (large : 33 ≤ S.ell) (B : Nat)
    (response : ∀ n : Nat, W S n → Q S n → Finset (Q S n))
    (bounded : ∀ (n : Nat) (g : W S n) (q : Q S n), (response n g q).card ≤ B) :
    ∃ (g : W S (budgetDepth B)) (q : Q S (budgetDepth B)),
      B < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S (budgetDepth B)) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q)-
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B))
          (backgroundRestriction S (budgetDepth B) g (response (budgetDepth B) g q)))
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) := by sorry
