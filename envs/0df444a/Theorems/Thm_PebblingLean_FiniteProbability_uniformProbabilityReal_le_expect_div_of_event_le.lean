-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_le_expect_div_of_event_le
-- name    : PebblingLean.FiniteProbability.uniformProbabilityReal_le_expect_div_of_event_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:43.674081+00:00
-- url     : https://prove2.me/theorems/a39484e2-bcc2-4067-a60d-0085556ebe37
-- title:
--   Finite Probability: uniform Probability Real le expect div of event le
-- statement:
--   Finite Markov inequality for uniform probability.  The event is allowed to
--   be any predicate implied by `a ≤ X`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L57-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L57-L86

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

theorem PebblingLean.FiniteProbability.uniformProbabilityReal_le_expect_div_of_event_le [Fintype Ω] [Nonempty Ω]
    {P : Ω → Prop} [DecidablePred P]
    (X : Ω → ℝ) {a : ℝ}
    (ha : 0 < a) (hnonneg : ∀ ω : Ω, 0 ≤ X ω)
    (hP : ∀ ω : Ω, P ω → a ≤ X ω) :
    uniformProbabilityReal P ≤ uniformExpectationReal X / a := by sorry
