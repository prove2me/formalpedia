-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_entropy_compProd__0c4dfbdef776
-- name    : P2M_ProbabilityTheory_Kernel_entropy_compProd__0c4dfbdef776
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:37:41.604971+00:00
-- url     : https://prove2.me/theorems/b713ba66-a8e5-4778-a695-132ce53cdf87
-- title:
--   P2 M Probability Theory Kernel entropy comp Prod  0c4dfbdef776: P2 M Probability Theory Kernel entropy comp Prod  0c4dfbdef776
-- statement:
--   The P2 M Probability Theory Kernel entropy comp Prod  0c4dfbdef776 construction uses the P2 M Probability Theory Kernel entropy comp Prod  0c4dfbdef776 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L288-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L288-L300

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

theorem P2M_ProbabilityTheory_Kernel_entropy_compProd__0c4dfbdef776 [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass T]
    [Countable T] [MeasurableSingletonClass U] {μ}
    [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ] := by sorry

alias «ProbabilityTheory».«Kernel».«entropy_compProd'» := P2M_ProbabilityTheory_Kernel_entropy_compProd__0c4dfbdef776
