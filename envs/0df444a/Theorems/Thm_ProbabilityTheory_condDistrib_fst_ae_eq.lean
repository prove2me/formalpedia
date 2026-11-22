-- Prove2me | Theorems.Thm_ProbabilityTheory_condDistrib_fst_ae_eq
-- name    : ProbabilityTheory.condDistrib_fst_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:31:37.225614+00:00
-- url     : https://prove2.me/theorems/3841ce97-0649-4a66-8455-b0a8ac756b92
-- title:
--   Probability Theory: cond Distrib fst ae eq
-- statement:
--   The Probability Theory construction uses the cond Distrib fst ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L266-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L266-L274

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

theorem ProbabilityTheory.condDistrib_fst_ae_eq
    [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib X Z μ := by sorry
