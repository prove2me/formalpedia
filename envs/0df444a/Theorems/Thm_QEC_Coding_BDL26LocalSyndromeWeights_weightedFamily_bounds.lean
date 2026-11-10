-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_weightedFamily_bounds
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.weightedFamily_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:37:00.449914+00:00
-- url     : https://prove2.me/theorems/289c68ae-d4f3-4b54-9e65-3806f44bd9a1
-- title:
--   BDL26 Local Syndrome Weights: weighted Family bounds
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the weighted Family bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L169-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L169-L175

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSyndromeWeights
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26ReplacementSupport BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26FiniteAlternatingCore BDL26DecodingGraph BDL26BoundedValence
open scoped BigOperators Classical

theorem QEC.Coding.BDL26LocalSyndromeWeights.weightedFamily_bounds {I : Type*} [Fintype I]
    (A : Finset (Word Bit I)) (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0)
    (M : ℕ) (hM : Fintype.card I ≤ M) :
    0 ≤ weightedFamily A t ∧ weightedFamily A t ≤
      (1 + Real.exp (-t)) ^ M - 1 := by sorry
