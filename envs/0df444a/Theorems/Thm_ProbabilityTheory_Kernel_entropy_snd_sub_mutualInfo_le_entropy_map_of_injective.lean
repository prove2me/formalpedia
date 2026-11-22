-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_snd_sub_mutualInfo_le_entropy_map_of_injective
-- name    : ProbabilityTheory.Kernel.entropy_snd_sub_mutualInfo_le_entropy_map_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:59.132583+00:00
-- url     : https://prove2.me/theorems/fe094fb9-4e19-47ab-8862-318c5ac88bf8
-- title:
--   Kernel: entropy snd sub mutual Info le entropy map of injective
-- statement:
--   The Kernel construction uses the entropy snd sub mutual Info le entropy map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L198-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L198-L230

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

theorem ProbabilityTheory.Kernel.entropy_snd_sub_mutualInfo_le_entropy_map_of_injective {V : Type*} [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ] (μ :
      Measure T) [IsZeroOrProbabilityMeasure μ]
    (f : S × U → V) (hfi : ∀ x, Injective (fun y ↦ f (x, y))) [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ f, μ] := by sorry
