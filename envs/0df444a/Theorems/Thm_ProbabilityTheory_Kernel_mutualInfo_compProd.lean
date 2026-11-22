-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_compProd
-- name    : ProbabilityTheory.Kernel.mutualInfo_compProd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:50.002076+00:00
-- url     : https://prove2.me/theorems/991c27eb-2a31-4c58-8433-081ee9a9f10a
-- title:
--   Kernel: mutual Info comp Prod
-- statement:
--   The Kernel construction uses the mutual Info comp Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L144-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L144-L150

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

theorem ProbabilityTheory.Kernel.mutualInfo_compProd
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) (hη :
      AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    Ik[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[snd (κ ⊗ₖ η), μ] - Hk[κ ⊗ₖ η, μ] := by sorry
