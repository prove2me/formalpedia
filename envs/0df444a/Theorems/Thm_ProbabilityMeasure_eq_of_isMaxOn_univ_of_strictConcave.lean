-- Prove2me | Theorems.Thm_ProbabilityMeasure_eq_of_isMaxOn_univ_of_strictConcave
-- name    : ProbabilityMeasure.eq_of_isMaxOn_univ_of_strictConcave
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:31.938571+00:00
-- url     : https://prove2.me/theorems/e5fb4757-1fd7-4c4a-be23-4d15afe08d95
-- title:
--   Probability Measure: eq of is Max On univ of strict Concave
-- statement:
--   Two global maximizers coincide if the function is strictly concave along convex combinations of
--   probability measures.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L34-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L34-L66

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ProbabilityMeasure
variable {α : Type*} [MeasurableSpace α]

theorem ProbabilityMeasure.eq_of_isMaxOn_univ_of_strictConcave
    {f : ProbabilityMeasure α → ℝ}
    (hStrict : ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
        f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
          (t : ℝ) * f p + (1 - (t : ℝ)) * f q)
    {p q : ProbabilityMeasure α}
    (hp : IsMaxOn f Set.univ p) (hq : IsMaxOn f Set.univ q) : p = q := by sorry
