-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416
-- name    : P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:31:22.78684+00:00
-- url     : https://prove2.me/theorems/b0a42a9f-fe57-4f2a-b8e2-5a976e87c49c
-- title:
--   P2 M Probability Theory cond Distrib apply  7130db3f8416: P2 M Probability Theory cond Distrib apply  7130db3f8416
-- statement:
--   The P2 M Probability Theory cond Distrib apply  7130db3f8416 construction uses the P2 M Probability Theory cond Distrib apply  7130db3f8416 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L220-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L220-L230

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]
variable [MeasurableSingletonClass T]
variable [Countable U] [DiscreteMeasurableSpace U]
variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

theorem P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416
    [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) {s : Set S} (hs :
      MeasurableSet s) :
    condDistrib X Y μ x s = (μ (Y ⁻¹' {x}))⁻¹ * μ (Y ⁻¹' {x} ∩ X ⁻¹' s) := by sorry

alias «ProbabilityTheory».«condDistrib_apply'» := P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416
