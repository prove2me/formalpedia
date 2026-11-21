-- Prove2me | Theorems.Thm_ProbabilityMeasure_convexCombination_comm
-- name    : ProbabilityMeasure.convexCombination_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:36.233026+00:00
-- url     : https://prove2.me/theorems/10207251-8c96-4383-a518-b2b43eb42bd2
-- title:
--   Probability Measure: convex Combination comm
-- statement:
--   The Probability Measure construction uses the convex Combination comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L68-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/StrictConcavity.lean#L68-L78

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

theorem ProbabilityMeasure.convexCombination_comm (p q : ProbabilityMeasure α) (t : NNReal) (ht : t ≤ 1) :
    ProbabilityMeasure.convexCombination p q t ht =
      ProbabilityMeasure.convexCombination q p (1 - t) (tsub_le_self) := by sorry
