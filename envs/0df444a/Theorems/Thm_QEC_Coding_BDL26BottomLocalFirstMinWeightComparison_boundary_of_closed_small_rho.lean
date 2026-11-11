-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_boundary_of_closed_small_rho
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.boundary_of_closed_small_rho
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:47.59194+00:00
-- url     : https://prove2.me/theorems/e8a95352-400f-47bd-8a7a-4780c899f213
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: boundary of closed small rho
-- statement:
--   The accepted explicit original H16 theorem is consumed on the entire parity word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L814-L820
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L814-L820

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.boundary_of_closed_small_rho (S : OddScale) (large : 16 ≤ S.half)
    (w : Error S) (hw : tannerCoboundary1 (P2 S) w = 0)
    (small : HammingWeight (rho S w) ≤ 14) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
