-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_lt_le_exp_neg_of_exponentialMoment_le
-- name    : PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_exp_neg_of_exponentialMoment_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:49:05.135196+00:00
-- url     : https://prove2.me/theorems/a3807617-a717-4c22-9b38-32fbbca7ece7
-- title:
--   Finite Probability: uniform Probability Real lt le exp neg of exponential Moment le
-- statement:
--   The Finite Probability construction uses the uniform Probability Real lt le exp neg of exponential Moment le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L117-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L117-L123

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

theorem PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_exp_neg_of_exponentialMoment_le [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam exponent : ℝ} (hlam : 0 < lam)
    (hmoment :
      uniformExpectationReal (fun ω : Ω => Real.exp (lam * (T - X ω))) ≤
        Real.exp (-exponent)) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤ Real.exp (-exponent) := by sorry
