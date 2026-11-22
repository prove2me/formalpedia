-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_compProd_swapLeft_prodMkLeft
-- name    : ProbabilityTheory.Kernel.compProd_swapLeft_prodMkLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:36:19.163876+00:00
-- url     : https://prove2.me/theorems/d7df01cf-0a35-4b12-b960-0861e246d94d
-- title:
--   Kernel: comp Prod swap Left prod Mk Left
-- statement:
--   The Kernel construction uses the comp Prod swap Left prod Mk Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L137-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L137-L143

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

theorem ProbabilityTheory.Kernel.compProd_swapLeft_prodMkLeft {α β γ : Type*} {mα : MeasurableSpace α} {mβ :
  MeasurableSpace β}
    {mγ : MeasurableSpace γ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    κ ⊗ₖ swapLeft (prodMkLeft β η) = κ ×ₖ η := by sorry
