-- Prove2me | Theorems.Thm_ProbabilityTheory_condDistrib_unit_right
-- name    : ProbabilityTheory.condDistrib_unit_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:38:14.51588+00:00
-- url     : https://prove2.me/theorems/bfb24f83-a0f0-4ed5-b16f-c0c3be0f8772
-- title:
--   Probability Theory: cond Distrib unit right
-- statement:
--   The Probability Theory construction uses the cond Distrib unit right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L396-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L396-L402

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
variable [Countable T]
variable [Nonempty T]

theorem ProbabilityTheory.condDistrib_unit_right [Nonempty S]
    (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    condDistrib X (fun _ ↦ ()) μ = Kernel.const Unit (μ.map X) := by sorry
