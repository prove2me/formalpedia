-- Prove2me | Theorems.Thm_ProbabilityMeasure_eq_left_of_convexCombination_eq
-- name    : ProbabilityMeasure.eq_left_of_convexCombination_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:28.689909+00:00
-- url     : https://prove2.me/theorems/a0d265c2-abe5-4bae-9dc2-498574eb9145
-- title:
--   Probability Measure: eq left of convex Combination eq
-- statement:
--   The Probability Measure construction uses the eq left of convex Combination eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L80-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L80-L115

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

theorem ProbabilityMeasure.eq_left_of_convexCombination_eq {p q : ProbabilityMeasure α} {t : NNReal}
    (ht_lt_one : t < 1)
    (h : ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) = p) :
    q = p := by sorry
