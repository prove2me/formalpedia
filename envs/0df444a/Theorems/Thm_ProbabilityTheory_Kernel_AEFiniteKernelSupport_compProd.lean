-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_compProd
-- name    : ProbabilityTheory.Kernel.AEFiniteKernelSupport.compProd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:33:27.59606+00:00
-- url     : https://prove2.me/theorems/27c9aa4e-135a-4f7d-aa17-9f69fd8a639e
-- title:
--   AEFinite Kernel Support: comp Prod
-- statement:
--   The AEFinite Kernel Support construction uses the comp Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L921-L936
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L921-L936

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
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

theorem ProbabilityTheory.Kernel.AEFiniteKernelSupport.compProd
    [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    {κ : Kernel T S} {η : Kernel (T × S) U} {μ : Measure T} [SFinite μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    AEFiniteKernelSupport (κ ⊗ₖ η) μ := by sorry
