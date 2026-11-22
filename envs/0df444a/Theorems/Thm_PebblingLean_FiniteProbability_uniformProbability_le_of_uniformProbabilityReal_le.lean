-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_uniformProbability_le_of_uniformProbabilityReal_le
-- name    : PebblingLean.FiniteProbability.uniformProbability_le_of_uniformProbabilityReal_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:05.81544+00:00
-- url     : https://prove2.me/theorems/7190a4da-c505-482b-b03d-46a7f91cac0f
-- title:
--   Finite Probability: uniform Probability le of uniform Probability Real le
-- statement:
--   The Finite Probability construction uses the uniform Probability le of uniform Probability Real le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L47-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L47-L53

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}

theorem PebblingLean.FiniteProbability.uniformProbability_le_of_uniformProbabilityReal_le [Fintype Ω]
    {P : Ω → Prop} [DecidablePred P] {eps : ℚ}
    (h : uniformProbabilityReal P ≤ (eps : ℝ)) :
    uniformProbability P ≤ eps := by sorry
