-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_boundary
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:22:28.329398+00:00
-- url     : https://prove2.me/theorems/db0a4b4f-ad59-49d5-937b-b43501adf46d
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: rho boundary
-- statement:
--   Compatibility with the actual entire C2 potential, including all X families.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L740-L745
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L740-L745

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_boundary (S : OddScale) (p : Word F (P2 S).X) :
    rho S (tannerCoboundary0 (P2 S) p) =
      tannerCoboundary0 (P1 S) (rzOldXParity (P1 S) S p) := by sorry
