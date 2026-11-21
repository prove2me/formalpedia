-- Prove2me | Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
-- name    : ProbabilityMeasure.convexCombination_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:36.931794+00:00
-- url     : https://prove2.me/theorems/84144365-6341-4027-8596-9f83f66482b3
-- title:
--   Probability Measure: convex Combination to Measure
-- statement:
--   The Probability Measure construction uses the convex Combination to Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L67-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L67-L71

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ProbabilityMeasure
variable {Ω : Type*} [MeasurableSpace Ω]

theorem ProbabilityMeasure.convexCombination_toMeasure (μ ν : ProbabilityMeasure Ω) (t : NNReal)
    (ht : t ≤ (1 : NNReal)) :
    (convexCombination μ ν t ht).toMeasure =
      t • μ.toMeasure + ((1 : NNReal) - t) • ν.toMeasure := by sorry

attribute [defeq] ProbabilityMeasure.convexCombination_toMeasure
