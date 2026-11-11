-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_local_or_weight
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_local_or_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:04.983511+00:00
-- url     : https://prove2.me/theorems/669bfd08-586d-492c-b83c-49ef0dbe07e6
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison local or weight
-- statement:
--   Literal first-branch locality OR full actual minimum-weight bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L602-L629
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L602-L629

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_local_or_weight (S : OddScale) (e : Error S) :
    levelTwoLocalError S
      (ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e)) ∨
    HammingWeight (ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e)) ≤
      HammingWeight e := by sorry
