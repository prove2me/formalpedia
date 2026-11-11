-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_agrees_of_local_preimage
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_agrees_of_local_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:27.833783+00:00
-- url     : https://prove2.me/theorems/5265ae5b-a2a7-4dc7-ba50-e5fc5070a430
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison agrees of local preimage
-- statement:
--   Every admissible local preimage forces EXACT agreement with original LOCAL-FIRST.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L591-L599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L591-L599

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_agrees_of_local_preimage (S : OddScale) (sigma : Syndrome S)
    (e : Error S) (he : levelTwoLocalError S e)
    (hs : tannerCoboundary1 (P2 S) e = sigma) :
    ownerFirstMinWeightFallback S sigma = decode S sigma := by sorry
