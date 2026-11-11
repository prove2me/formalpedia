-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_chain_boundary_iff
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.chain_boundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:08:11.263316+00:00
-- url     : https://prove2.me/theorems/b8585ae9-d134-48ba-bcfd-099c11228c47
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: chain boundary iff
-- statement:
--   Original code membership and the full original Tanner range are the same object.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L644-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L644-L657

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.chain_boundary_iff (S : OddScale) (w : Error S) :
    w ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier ↔
      w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
