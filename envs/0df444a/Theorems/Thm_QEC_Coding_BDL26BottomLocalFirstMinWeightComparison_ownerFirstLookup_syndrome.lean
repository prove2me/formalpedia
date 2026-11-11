-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_ownerFirstLookup_syndrome
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstLookup_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:20:09.921332+00:00
-- url     : https://prove2.me/theorems/01092605-d84a-4fb0-8c10-a401eccbfaa2
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: owner First Lookup syndrome
-- statement:
--   The BDL26 Bottom Local First Min Weight Comparison construction uses the owner First Lookup syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L525-L539
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L525-L539

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstLookup_syndrome {E Z : Type} [DecidableEq Z]
    (entries : List E) (syndrome : E → Z) (isLocal : E → Bool)
    (weight : E → Nat) (fallback : E) (sigma : Z)
    (hex : ∃ b ∈ entries, syndrome b = sigma) :
    syndrome (ownerFirstLookup entries syndrome isLocal weight fallback sigma) = sigma := by sorry
