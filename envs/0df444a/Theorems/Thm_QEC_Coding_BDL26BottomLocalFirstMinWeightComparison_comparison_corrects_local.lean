-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_corrects_local
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_local
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T07:17:04.301548+00:00
-- url     : https://prove2.me/theorems/4c8b28cd-d1d1-4992-b488-097579cba984
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison corrects local
-- statement:
--   Current F17 owner-local correctness is preserved for every original scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L660-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L660-L665

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_local (S : OddScale) (e : Error S)
    (he : levelTwoLocalError S e) :
    e + ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
