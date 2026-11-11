-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_corrects_radius_code
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_radius_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T08:32:41.935193+00:00
-- url     : https://prove2.me/theorems/60f56a99-3461-4cd1-bbf8-99ae903b49d7
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison corrects radius code
-- statement:
--   The same full-word radius theorem in the original C2 check-code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1298-L1302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1298-L1302

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_radius_code (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e : Error S) (small : HammingWeight e ≤ r) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by sorry
