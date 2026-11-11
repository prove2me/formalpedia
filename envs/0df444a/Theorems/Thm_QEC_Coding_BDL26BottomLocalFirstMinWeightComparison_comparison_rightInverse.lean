-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_rightInverse
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_rightInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:49:03.301288+00:00
-- url     : https://prove2.me/theorems/48d8a4f9-e566-4cdd-a606-bb8653cac72c
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: comparison right Inverse
-- statement:
--   Right inverse on the actual full represented syndrome domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L578-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L578-L588

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_rightInverse (S : OddScale) (sigma : Syndrome S)
    (hsigma : sigma ∈ LinearMap.range (tannerCoboundary1 (P2 S))) :
    tannerCoboundary1 (P2 S) (ownerFirstMinWeightFallback S sigma) = sigma := by sorry
