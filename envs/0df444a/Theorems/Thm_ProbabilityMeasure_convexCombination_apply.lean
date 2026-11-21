-- Prove2me | Theorems.Thm_ProbabilityMeasure_convexCombination_apply
-- name    : ProbabilityMeasure.convexCombination_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:39.288507+00:00
-- url     : https://prove2.me/theorems/ed9dd997-d369-4455-9a4c-c14730b3f842
-- title:
--   Probability Measure: convex Combination apply
-- statement:
--   The Probability Measure construction uses the convex Combination apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L73-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean#L73-L78

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

theorem ProbabilityMeasure.convexCombination_apply (μ ν : ProbabilityMeasure Ω) (t : NNReal)
    (ht : t ≤ (1 : NNReal))
    {s : Set Ω} (_hs : MeasurableSet s) :
    (convexCombination μ ν t ht).toMeasure s =
      (t : ENNReal) * μ.toMeasure s + (((1 : NNReal) - t : NNReal) : ENNReal) * ν.toMeasure s := by sorry
