-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_condKernel_le_entropy_snd
-- name    : ProbabilityTheory.Kernel.entropy_condKernel_le_entropy_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:48:34.539111+00:00
-- url     : https://prove2.me/theorems/94f65b41-6d6d-4582-bf02-036f22e48862
-- title:
--   Kernel: entropy cond Kernel le entropy snd
-- statement:
--   The Kernel construction uses the entropy cond Kernel le entropy snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L189-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L189-L195

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]
variable [MeasurableSingletonClass T]
variable [Countable S] [Countable T]
variable [Countable U]

theorem ProbabilityTheory.Kernel.entropy_condKernel_le_entropy_snd [Nonempty U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[condKernel κ, μ ⊗ₘ (fst κ)] ≤ Hk[snd κ, μ] := by sorry
