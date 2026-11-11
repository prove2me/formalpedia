-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_tanner_d1_d0
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.tanner_d1_d0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:22:40.102756+00:00
-- url     : https://prove2.me/theorems/5fa1a3d4-e5dd-4762-9e08-c23dc1cb2872
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: tanner d1 d0
-- statement:
--   Actual full differentials square to zero; no caller exactness certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L729-L731
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L729-L731

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.tanner_d1_d0 (P : TannerSquarePresentation) (p : Word F P.X) :
    tannerCoboundary1 P (tannerCoboundary0 P p) = 0 := by sorry
