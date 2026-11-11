-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_boundary_of_closed_rho_weight
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.boundary_of_closed_rho_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:18:53.881144+00:00
-- url     : https://prove2.me/theorems/15e4f693-afd8-4f3b-ae40-1d20ad83443e
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: boundary of closed rho weight
-- statement:
--   Scale-dependent exactness is applied to the entire actual RZ parity word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1241-L1248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L1241-L1248

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.boundary_of_closed_rho_weight (S : OddScale) (k : Nat)
    (large : k+2 ≤ S.half) (w : Error S)
    (closed : tannerCoboundary1 (P2 S) w=0)
    (small : HammingWeight (rho S w) ≤ k) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by sorry
