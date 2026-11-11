-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparisonBaseAdapter_correctsLocalErrors
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparisonBaseAdapter_correctsLocalErrors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T07:17:48.777436+00:00
-- url     : https://prove2.me/theorems/5d5fd0b1-3f56-4653-8a06-e692cba33bed
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison Base Adapter corrects Local Errors
-- statement:
--   The BDL26 Bottom Local First Min Weight Comparison construction uses the comparison Base Adapter corrects Local Errors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L889-L898
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L889-L898

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparisonBaseAdapter_correctsLocalErrors (S : OddScale) :
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) := by sorry
