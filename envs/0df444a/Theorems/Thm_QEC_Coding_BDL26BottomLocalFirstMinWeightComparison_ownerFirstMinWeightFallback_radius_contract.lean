-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_ownerFirstMinWeightFallback_radius_contract
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback_radius_contract
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T11:46:46.689363+00:00
-- url     : https://prove2.me/theorems/fad23de4-1170-47f0-994e-2b72a554ef61
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: owner First Min Weight Fallback radius contract
-- statement:
--   All original F17 properties together with scale-dependent full-word correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1305-L1314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1305-L1314

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback_radius_contract (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) :
    ownerFirstMinWeightFallback S 0 = 0 ∧
    (comparisonBaseAdapter S).IsRightInverse ∧
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) ∧
    ∀ e : Error S, HammingWeight e ≤ r →
      e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
        (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by sorry
