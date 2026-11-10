-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSyndromeWeights_rxWeightFactor_bounds
-- name    : QEC.Coding.BDL26LocalSyndromeWeights.rxWeightFactor_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:10:23.04856+00:00
-- url     : https://prove2.me/theorems/84873445-4854-4f59-a16c-21a54089f9fa
-- title:
--   BDL26 Local Syndrome Weights: rx Weight Factor bounds
-- statement:
--   The BDL26 Local Syndrome Weights construction uses the rx Weight Factor bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L309-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalSyndromeWeights.lean#L309-L321

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

theorem QEC.Coding.BDL26LocalSyndromeWeights.rxWeightFactor_bounds (P : TannerSquarePresentation) (hP : BoundedValence P)
    (S : OddScale) (u : Vertex P) (A : Finset (Word Bit (RXFiber P S u)))
    (t : ℝ) (hA : ∀ x ∈ A, x ≠ 0) :
    0 ≤ rxWeightFactor P S u A t ∧ rxWeightFactor P S u A t ≤
      (1 + Real.exp (-t)) ^ (14 * S.ell^2) - 1 := by sorry
