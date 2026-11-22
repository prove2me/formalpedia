-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_reverse
-- name    : ProbabilityTheory.Kernel.entropy_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:23.442062+00:00
-- url     : https://prove2.me/theorems/6176deec-a233-49a8-9220-b52d28aad4af
-- title:
--   Kernel: entropy reverse
-- statement:
--   The Kernel construction uses the entropy reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L241-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L241-L254

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_reverse

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]

theorem ProbabilityTheory.Kernel.entropy_reverse
    {κ : Kernel T (S × U × V)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[reverse κ, μ] = Hk[κ, μ] := by sorry
