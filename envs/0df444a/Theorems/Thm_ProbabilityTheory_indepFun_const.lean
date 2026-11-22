-- Prove2me | Theorems.Thm_ProbabilityTheory_indepFun_const
-- name    : ProbabilityTheory.indepFun_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:35.184058+00:00
-- url     : https://prove2.me/theorems/e168ebe4-d3c0-4579-88c0-ba810260ebda
-- title:
--   Probability Theory: indep Fun const
-- statement:
--   Random variables are always independent of constants.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L174-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L174-L181

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]

theorem ProbabilityTheory.indepFun_const
    [IsZeroOrProbabilityMeasure μ] (c : α) : IndepFun f (fun _ => c) μ := by sorry
