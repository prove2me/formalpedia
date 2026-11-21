-- Prove2me | Theorems.Thm_ProbabilityMeasure_eq_right_of_convexCombination_eq
-- name    : ProbabilityMeasure.eq_right_of_convexCombination_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:33.088379+00:00
-- url     : https://prove2.me/theorems/60335c97-3216-4b53-a5e1-56bc2baa1e47
-- title:
--   Probability Measure: eq right of convex Combination eq
-- statement:
--   The Probability Measure construction uses the eq right of convex Combination eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L117-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L117-L130

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

theorem ProbabilityMeasure.eq_right_of_convexCombination_eq {p q : ProbabilityMeasure α} {t : NNReal}
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (h : ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) = q) :
    p = q := by sorry
