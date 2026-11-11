-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_state_rx_source_bounds
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.state_rx_source_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:52:52.163023+00:00
-- url     : https://prove2.me/theorems/5880864d-a5c0-42d8-b68f-d241d09d6791
-- title:
--   BDL26 Local Syndrome Weights: state rx source bounds
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the state rx source bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L359-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L359-L365

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.state_rx_source_bounds (S : OddScale) (n : ℕ)
    (u : Vertex (state S n).presentation)
    (A : Finset (Word Bit (RXFiber (state S n).presentation S u)))
    (beta : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor (state S n).presentation S u A (beta/4) ∧
      rxWeightFactor (state S n).presentation S u A (beta/4) ≤ sourceEnvelope S beta := by sorry
