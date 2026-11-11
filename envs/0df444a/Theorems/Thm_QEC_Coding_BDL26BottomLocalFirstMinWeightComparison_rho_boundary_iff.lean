-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_boundary_iff
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_boundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:53.115389+00:00
-- url     : https://prove2.me/theorems/11f9c6e5-1357-45f7-bbd1-4e9d07ee754f
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: rho boundary iff
-- statement:
--   Full cohomology detection, by constructing the whole residual potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L762-L811
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L762-L811

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_boundary_iff (S : OddScale) (w : Error S)
    (hw : tannerCoboundary1 (P2 S) w = 0) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) ↔
      rho S w ∈ LinearMap.range (tannerCoboundary0 (P1 S)) := by sorry
