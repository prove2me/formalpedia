-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_local_weight_le_one
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_local_weight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:42.230107+00:00
-- url     : https://prove2.me/theorems/3d62e1d1-9f53-40bc-8a7d-b4a672f83515
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: rho local weight le one
-- statement:
--   Large owner-local corrections still cost at most one OLD parity coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L716-L726
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L716-L726

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_local_weight_le_one (S : OddScale) (w : Error S)
    (hw : levelTwoLocalError S w) : HammingWeight (rho S w) ≤ 1 := by sorry
