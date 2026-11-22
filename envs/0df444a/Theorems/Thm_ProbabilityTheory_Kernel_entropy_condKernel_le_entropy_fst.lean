-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_condKernel_le_entropy_fst
-- name    : ProbabilityTheory.Kernel.entropy_condKernel_le_entropy_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:50:11.7362+00:00
-- url     : https://prove2.me/theorems/fabc26c1-4c19-459e-a1d2-0e4d8df46804
-- title:
--   Kernel: entropy cond Kernel le entropy fst
-- statement:
--   The Kernel construction uses the entropy cond Kernel le entropy fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L181-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L181-L187

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_swapRight

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

theorem ProbabilityTheory.Kernel.entropy_condKernel_le_entropy_fst [Nonempty S]
    (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] ≤ Hk[fst κ, μ] := by sorry
