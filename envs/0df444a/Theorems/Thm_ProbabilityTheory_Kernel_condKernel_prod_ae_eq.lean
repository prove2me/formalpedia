-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_condKernel_prod_ae_eq
-- name    : ProbabilityTheory.Kernel.condKernel_prod_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:36:21.202799+00:00
-- url     : https://prove2.me/theorems/25149290-4034-4d99-9b4f-543396230df8
-- title:
--   Kernel: cond Kernel prod ae eq
-- statement:
--   The Kernel construction uses the cond Kernel prod ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L145-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L145-L149

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

theorem ProbabilityTheory.Kernel.condKernel_prod_ae_eq (κ : Kernel T S) [IsFiniteKernel κ] {μ}
    (η : Kernel T U) [IsMarkovKernel η] :
    condKernel (κ ×ₖ η) =ᵐ[μ ⊗ₘ κ] prodMkRight S η := by sorry
