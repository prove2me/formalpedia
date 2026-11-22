-- Prove2me | Theorems.Thm_ProbabilityTheory_uniformOn_apply_eq_zero
-- name    : ProbabilityTheory.uniformOn_apply_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:04.56107+00:00
-- url     : https://prove2.me/theorems/d014257e-78bd-46f5-b267-11476c257bec
-- title:
--   Probability Theory: uniform On apply eq zero
-- statement:
--   The Probability Theory construction uses the uniform On apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L45-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean#L45-L48

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

theorem ProbabilityTheory.uniformOn_apply_eq_zero (hst : s ∩ t = ∅) : uniformOn s t = 0 := by sorry
