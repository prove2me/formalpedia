-- Prove2me | Theorems.Thm_ProbabilityTheory_real_uniformOn_apply_singleton_of_not_mem
-- name    : ProbabilityTheory.real_uniformOn_apply_singleton_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:39:40.817799+00:00
-- url     : https://prove2.me/theorems/d205cd27-6fef-4a89-b538-65a51ea5a2b8
-- title:
--   Probability Theory: real uniform On apply singleton of not mem
-- statement:
--   The Probability Theory construction uses the real uniform On apply singleton of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L41-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L41-L43

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

theorem ProbabilityTheory.real_uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) :
    (uniformOn s).real {x} = 0 := by sorry
