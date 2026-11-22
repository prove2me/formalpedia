-- Prove2me | Theorems.Thm_ProbabilityTheory_uniformOn_apply_singleton_of_not_mem
-- name    : ProbabilityTheory.uniformOn_apply_singleton_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:04.077806+00:00
-- url     : https://prove2.me/theorems/d5004ec7-0726-40a7-939b-6cc7bee7ed2c
-- title:
--   Probability Theory: uniform On apply singleton of not mem
-- statement:
--   The Probability Theory construction uses the uniform On apply singleton of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L38-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L38-L39

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure
open ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}

theorem ProbabilityTheory.uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) : uniformOn s {x} = 0 := by sorry
