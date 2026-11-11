-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_small_error_local_preimage
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.small_error_local_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:24:13.700732+00:00
-- url     : https://prove2.me/theorems/71af4fc3-cbaa-46c3-85fa-595997455cdc
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: small error local preimage
-- statement:
--   ANY same-syndrome owner-local preimage, even of large physical weight, works.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L823-L836
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L823-L836

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.small_error_local_preimage (S : OddScale) (large : 16 ≤ S.half)
    (e c : Error S) (small : HammingWeight e ≤ 7) (hlocal : levelTwoLocalError S c)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
