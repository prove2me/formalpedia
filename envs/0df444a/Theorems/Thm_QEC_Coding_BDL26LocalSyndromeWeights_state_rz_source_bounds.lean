-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_state_rz_source_bounds
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.state_rz_source_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:51:28.329293+00:00
-- url     : https://prove2.me/theorems/a4099b4f-2ad6-4bd8-8a1d-1315f86e2a6e
-- title:
--   BDL26 Local Syndrome Weights: state rz source bounds
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the state rz source bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L367-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L367-L372

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.state_rz_source_bounds (S : OddScale) (n : ℕ) (z : (state S n).presentation.Z)
    (A : Finset (Word Bit (RZFiber (state S n).presentation S z)))
    (beta : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rzWeightFactor (state S n).presentation S z A (beta/4) ∧
      rzWeightFactor (state S n).presentation S z A (beta/4) ≤ sourceEnvelope S beta := by sorry
