-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_ownerFirstLookup_fallback_weight
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstLookup_fallback_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:21:47.80055+00:00
-- url     : https://prove2.me/theorems/55c44df9-9c74-4e26-a055-eb22bd47c550
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: owner First Lookup fallback weight
-- statement:
--   The BDL26 Bottom Local First Min Weight Comparison construction uses the owner First Lookup fallback weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L553-L562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L553-L562

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstLookup_fallback_weight {E Z : Type} [DecidableEq Z]
    (entries : List E) (syndrome : E → Z) (isLocal : E → Bool)
    (weight : E → Nat) (fallback : E) (sigma : Z) (b : E)
    (hb : b ∈ entries) (hs : syndrome b = sigma)
    (hl : search (fun e => isLocal e && decide (syndrome e = sigma)) entries = none) :
    weight (ownerFirstLookup entries syndrome isLocal weight fallback sigma) ≤ weight b := by sorry
