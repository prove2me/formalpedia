-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_condKernel_map_prodMk_left
-- name    : ProbabilityTheory.Kernel.condKernel_map_prodMk_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:36:24.975364+00:00
-- url     : https://prove2.me/theorems/c7b8d838-fccb-4c24-98f5-4c615d360d0c
-- title:
--   Kernel: cond Kernel map prod Mk left
-- statement:
--   The Kernel construction uses the cond Kernel map prod Mk left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L158-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L158-L207

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
open ProbabilityTheory.Kernel
variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]
variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]

theorem ProbabilityTheory.Kernel.condKernel_map_prodMk_left {V : Type*} [Nonempty V] [MeasurableSpace V]
    [DiscreteMeasurableSpace V] [Countable V]
    (κ : Kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T)
    (f : S × U → V) :
    condKernel (map κ (fun p ↦ (p.1, f p)))
      =ᵐ[μ ⊗ₘ fst κ] snd ((condKernel κ) ⊗ₖ (deterministic (fun x :
        (T × S) × U ↦ f (x.1.2, x.2))
          .of_discrete)) := by sorry
