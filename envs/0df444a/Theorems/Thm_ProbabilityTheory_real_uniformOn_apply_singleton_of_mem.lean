-- Prove2me | Theorems.Thm_ProbabilityTheory_real_uniformOn_apply_singleton_of_mem
-- name    : ProbabilityTheory.real_uniformOn_apply_singleton_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:30:57.12369+00:00
-- url     : https://prove2.me/theorems/6981434f-e5a4-4e05-acd3-7e412c481cee
-- title:
--   Probability Theory: real uniform On apply singleton of mem
-- statement:
--   The Probability Theory construction uses the real uniform On apply singleton of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L34-L36
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L34-L36

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

theorem ProbabilityTheory.real_uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    (uniformOn s).real {x} = 1 / Nat.card s := by sorry
