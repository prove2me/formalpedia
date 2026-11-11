-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_lifted_boundary
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.lifted_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:22:58.474301+00:00
-- url     : https://prove2.me/theorems/f617deee-62f7-414d-82d3-60a4cdcc30d5
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: lifted boundary
-- statement:
--   Old full boundaries lift through the actual selected RZ map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L748-L759
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L748-L759

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.lifted_boundary (S : OddScale) (p : Word F (P1 S).X) :
    tannerCoboundary0 (P2 S) (rzMap0Coord (P1 S) S p) =
      map1Coord (P1 S) (rxState S baseState).admissible S
        (tannerCoboundary0 (P1 S) p) := by sorry
