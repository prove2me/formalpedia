-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparisonBaseAdapter_rightInverse
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparisonBaseAdapter_rightInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:53.705091+00:00
-- url     : https://prove2.me/theorems/5d9d6f73-d6ca-4a6e-8baf-844fcb31d9e6
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison Base Adapter right Inverse
-- statement:
--   The BDL26 Bottom Local First Min Weight Comparison construction uses the comparison Base Adapter right Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L875-L887
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L875-L887

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparisonBaseAdapter_rightInverse (S : OddScale) :
    (comparisonBaseAdapter S).IsRightInverse := by sorry
