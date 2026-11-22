-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_finiteSupport_of_compProd__3c7ae9225083
-- name    : P2M_ProbabilityTheory_Kernel_finiteSupport_of_compProd__3c7ae9225083
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:35:21.958874+00:00
-- url     : https://prove2.me/theorems/a17044f8-a80f-4c3d-a381-11e32126ee46
-- title:
--   P2 M Probability Theory Kernel finite Support of comp Prod  3c7ae9225083: P2 M Probability Theory Kernel finite Support of comp Prod  3c7ae9225083
-- statement:
--   Composing a finitely supported measure with a finitely supported kernel gives a
--   finitely
--   supported kernel.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L84-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/Basic.lean#L84-L95

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

theorem P2M_ProbabilityTheory_Kernel_finiteSupport_of_compProd__3c7ae9225083 [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    FiniteSupport (μ ⊗ₘ κ) := by sorry

alias «ProbabilityTheory».«Kernel».«finiteSupport_of_compProd'» := P2M_ProbabilityTheory_Kernel_finiteSupport_of_compProd__3c7ae9225083
