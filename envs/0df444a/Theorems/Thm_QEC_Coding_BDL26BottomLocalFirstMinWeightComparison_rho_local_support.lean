-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_local_support
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_local_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:21:28.018876+00:00
-- url     : https://prove2.me/theorems/c2f03617-80e4-4adf-bfad-d135f8c453a6
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: rho local support
-- statement:
--   All actual owner kinds are retained: X/Z owners give zero parity everywhere.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L704-L713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L704-L713

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_local_support (S : OddScale) (w : Error S)
    (hw : levelTwoLocalError S w) :
    ∃ a : (P1 S).Q, ∀ q, q ≠ a → rho S w q = 0 := by sorry
