-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd___39a21c44794a
-- name    : P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd___39a21c44794a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:48:36.061538+00:00
-- url     : https://prove2.me/theorems/ab9ab04a-f612-4fc5-9157-0039044b6040
-- title:
--   P2 M Probability Theory Kernel Measure comp Prod comp Prod   39a21c44794a: P2 M Probability Theory Kernel Measure comp Prod comp Prod   39a21c44794a
-- statement:
--   The P2 M Probability Theory Kernel Measure comp Prod comp Prod   39a21c44794a construction uses the P2 M Probability Theory Kernel Measure comp Prod comp Prod   39a21c44794a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L103-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L103-L110

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

theorem P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd___39a21c44794a (μ : Measure T)
    (ξ : Kernel T S) (κ : Kernel (T × S) U) :
    μ ⊗ₘ ξ ⊗ₘ κ = Measure.comap MeasurableEquiv.prodAssoc (μ ⊗ₘ (ξ ⊗ₖ κ)) := by sorry

alias «ProbabilityTheory».«Kernel».«Measure».«compProd_compProd''» := P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd___39a21c44794a
