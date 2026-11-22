-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_chain_rule__5854b667e2d9
-- name    : P2M_ProbabilityTheory_Kernel_chain_rule__5854b667e2d9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:33:11.489337+00:00
-- url     : https://prove2.me/theorems/bef7e1fa-d0d3-4647-bba8-683f2ad0749d
-- title:
--   P2 M Probability Theory Kernel chain rule  5854b667e2d9: P2 M Probability Theory Kernel chain rule  5854b667e2d9
-- statement:
--   The P2 M Probability Theory Kernel chain rule  5854b667e2d9 construction uses the P2 M Probability Theory Kernel chain rule  5854b667e2d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L355-L362
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L355-L362

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_swapRight

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

theorem P2M_ProbabilityTheory_Kernel_chain_rule__5854b667e2d9 [Nonempty S] [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] = Hk[snd κ, μ] + Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] := by sorry

alias «ProbabilityTheory».«Kernel».«chain_rule'» := P2M_ProbabilityTheory_Kernel_chain_rule__5854b667e2d9
