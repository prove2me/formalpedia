-- Prove2me | Theorems.Thm_ProbabilityTheory_uniformOn_real_singleton
-- name    : ProbabilityTheory.uniformOn_real_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:39:53.819612+00:00
-- url     : https://prove2.me/theorems/84d1b79c-bcb7-4789-81f0-c41f7666faca
-- title:
--   Probability Theory: uniform On real singleton
-- statement:
--   The Probability Theory construction uses the uniform On real singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L62-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L62-L64

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

theorem ProbabilityTheory.uniformOn_real_singleton (hs : s.Finite) (ω : Ω) [Decidable (ω ∈ s)] :
    (uniformOn s).real {ω} = if ω ∈ s then (s.ncard : ℝ)⁻¹ else 0 := by sorry
