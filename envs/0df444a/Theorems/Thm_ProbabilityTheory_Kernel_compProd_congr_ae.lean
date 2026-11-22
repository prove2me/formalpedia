-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_compProd_congr_ae
-- name    : ProbabilityTheory.Kernel.compProd_congr_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:34:30.928833+00:00
-- url     : https://prove2.me/theorems/3ae7d3fc-d915-4cf4-84c7-921fb53957a2
-- title:
--   Kernel: comp Prod congr ae
-- statement:
--   The Kernel construction uses the comp Prod congr ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L573-L584
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L573-L584

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

theorem ProbabilityTheory.Kernel.compProd_congr_ae {μ} [SFinite μ] {κ κ' :
  Kernel T S} [IsSFiniteKernel κ] [IsSFiniteKernel κ']
    {η η' : Kernel (T × S) U} [IsSFiniteKernel η] [IsSFiniteKernel η']
    (hκ : κ =ᵐ[μ] κ') (hη : η =ᵐ[μ ⊗ₘ κ] η') :
    κ ⊗ₖ η =ᵐ[μ] κ' ⊗ₖ η' := by sorry
