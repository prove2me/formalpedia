-- Prove2me | Theorems.Thm_ProbabilityTheory_uniformOn_of_infinite
-- name    : ProbabilityTheory.uniformOn_of_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:04.59041+00:00
-- url     : https://prove2.me/theorems/b70aeb5b-7ad9-419e-a4ba-ffb0672f2645
-- title:
--   Probability Theory: uniform On of infinite
-- statement:
--   The Probability Theory construction uses the uniform On of infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L50-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L50-L50

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

theorem ProbabilityTheory.uniformOn_of_infinite (hs : s.Infinite) : uniformOn s = 0 := by sorry
