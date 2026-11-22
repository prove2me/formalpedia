-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_entropy_prodMkRight__0c3a7da877c3
-- name    : P2M_ProbabilityTheory_Kernel_entropy_prodMkRight__0c3a7da877c3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:41:40.807857+00:00
-- url     : https://prove2.me/theorems/a22da3cf-6475-4c19-bf74-7f9e13fa703a
-- title:
--   P2 M Probability Theory Kernel entropy prod Mk Right  0c3a7da877c3: P2 M Probability Theory Kernel entropy prod Mk Right  0c3a7da877c3
-- statement:
--   The P2 M Probability Theory Kernel entropy prod Mk Right  0c3a7da877c3 construction uses the P2 M Probability Theory Kernel entropy prod Mk Right  0c3a7da877c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L374-L382
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L374-L382

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_prodMkRight

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

theorem P2M_ProbabilityTheory_Kernel_entropy_prodMkRight__0c3a7da877c3 [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T]
    {η : Kernel T U}
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    Hk[prodMkRight S η, μ.prod ν] = Hk[η, μ] := by sorry

alias «ProbabilityTheory».«Kernel».«entropy_prodMkRight'» := P2M_ProbabilityTheory_Kernel_entropy_prodMkRight__0c3a7da877c3
