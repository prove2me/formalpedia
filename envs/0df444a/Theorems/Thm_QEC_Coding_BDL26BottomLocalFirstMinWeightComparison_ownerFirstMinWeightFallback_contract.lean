-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_ownerFirstMinWeightFallback_contract
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback_contract
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T11:37:00.906708+00:00
-- url     : https://prove2.me/theorems/61653093-1e57-44e8-b403-95c8b0f8c077
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: owner First Min Weight Fallback contract
-- statement:
--   One complete separately named comparison contract; no canonical adoption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L901-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L901-L909

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback_contract (S : OddScale) (large : 16 ≤ S.half) :
    ownerFirstMinWeightFallback S 0 = 0 ∧
    (comparisonBaseAdapter S).IsRightInverse ∧
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) ∧
    ∀ e : Error S, HammingWeight e ≤ 7 →
      e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
        (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by sorry
