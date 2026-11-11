-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_corrects_radius
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_radius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T08:31:06.071208+00:00
-- url     : https://prove2.me/theorems/bc46793f-9b3b-460c-aea9-9d7c6899b3c1
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison corrects radius
-- statement:
--   The unchanged comparison decoder corrects every full physical error of weight≤r.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1288-L1295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1288-L1295

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_radius (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e : Error S) (small : HammingWeight e ≤ r) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
