-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_lt_le_of_exponentialMoment_le
-- name    : PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_of_exponentialMoment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:21.585508+00:00
-- url     : https://prove2.me/theorems/f901e0aa-13d9-42de-8506-5cb9c212743f
-- title:
--   Finite Probability: uniform Probability Real lt le of exponential Moment le
-- statement:
--   The Finite Probability construction uses the uniform Probability Real lt le of exponential Moment le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L110-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L110-L115

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

theorem PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_of_exponentialMoment_le [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam B : ℝ} (hlam : 0 < lam)
    (hmoment :
      uniformExpectationReal (fun ω : Ω => Real.exp (lam * (T - X ω))) ≤ B) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤ B := by sorry
