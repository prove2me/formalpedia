-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_state_rxWeightFactor_bounds
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.state_rxWeightFactor_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:10:34.909303+00:00
-- url     : https://prove2.me/theorems/43c4a2c1-d529-41e8-8105-6e35312e08c0
-- title:
--   BDL26 Local Syndrome Weights: state rx Weight Factor bounds
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the state rx Weight Factor bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L337-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L337-L344

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.state_rxWeightFactor_bounds (S : OddScale) (n : ℕ)
    (u : Vertex (state S n).presentation)
    (A : Finset (Word Bit (RXFiber (state S n).presentation S u)))
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor (state S n).presentation S u A t ∧
      rxWeightFactor (state S n).presentation S u A t ≤
        (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 := by sorry
