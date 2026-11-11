-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_radius_error_local_preimage
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.radius_error_local_preimage
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T08:30:30.985192+00:00
-- url     : https://prove2.me/theorems/79be1c7a-169b-40a2-8155-ad9060271e0e
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: radius error local preimage
-- statement:
--   ANY same-syndrome owner-local preimage, with no physical-weight bound on it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1251-L1270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1251-L1270

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.radius_error_local_preimage (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e c : Error S)
    (small : HammingWeight e ≤ r) (hlocal : levelTwoLocalError S c)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
