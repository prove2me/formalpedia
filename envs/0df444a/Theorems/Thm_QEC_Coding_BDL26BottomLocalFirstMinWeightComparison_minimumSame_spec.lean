-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_minimumSame_spec
-- name    : QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.minimumSame_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:48:46.144983+00:00
-- url     : https://prove2.me/theorems/9f7858a6-0974-4d58-8846-3479e6c6f253
-- title:
--   BDL26 Bottom Local First Min Weight Comparison: minimum Same spec
-- statement:
--   The complete recursion invariant proves membership, syndrome and minimum weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L452-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BottomLocalFirstMinWeightComparison.lean#L452-L501

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

theorem QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.minimumSame_spec {E Z : Type} [DecidableEq Z]
    (syndrome : E → Z) (weight : E → Nat) (sigma : Z) (entries : List E) :
    match minimumSame syndrome weight sigma entries with
    | none => ∀ b ∈ entries, syndrome b ≠ sigma
    | some a => a ∈ entries ∧ syndrome a = sigma ∧
        ∀ b ∈ entries, syndrome b = sigma → weight a ≤ weight b := by sorry
