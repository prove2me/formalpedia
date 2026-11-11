-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_radius_error_light_preimage
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.radius_error_light_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:30:58.025255+00:00
-- url     : https://prove2.me/theorems/9b171445-03cf-4a27-a23d-ae7969dffa74
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: radius error light preimage
-- statement:
--   ANY full same-syndrome preimage no heavier than e has parity weight at most 2r.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1273-L1285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1273-L1285

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.radius_error_light_preimage (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e c : Error S)
    (small : HammingWeight e ≤ r) (light : HammingWeight c ≤ HammingWeight e)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
