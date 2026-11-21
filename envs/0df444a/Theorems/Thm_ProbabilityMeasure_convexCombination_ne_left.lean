-- Prove2me | Theorems.Thm_ProbabilityMeasure_convexCombination_ne_left
-- name    : ProbabilityMeasure.convexCombination_ne_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:30.868323+00:00
-- url     : https://prove2.me/theorems/837d4e95-08e7-437e-a62a-ae22fd9310ba
-- title:
--   Probability Measure: convex Combination ne left
-- statement:
--   The Probability Measure construction uses the convex Combination ne left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L132-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L132-L136

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

theorem ProbabilityMeasure.convexCombination_ne_left {p q : ProbabilityMeasure α} (h_ne : p ≠ q) {t : NNReal}
    (ht_lt_one : t < 1) :
    ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) ≠ p := by sorry
