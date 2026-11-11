-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_minimumSame_exists
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.minimumSame_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:17:00.866252+00:00
-- url     : https://prove2.me/theorems/70c6e747-6ab2-4023-9aad-7c0078376870
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: minimum Same exists
-- statement:
--   A represented syndrome excludes the default and gives a real minimum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L504-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L504-L515

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.minimumSame_exists {E Z : Type} [DecidableEq Z]
    (syndrome : E → Z) (weight : E → Nat) (sigma : Z) (entries : List E)
    (hex : ∃ b ∈ entries, syndrome b = sigma) :
    ∃ a, minimumSame syndrome weight sigma entries = some a := by sorry
