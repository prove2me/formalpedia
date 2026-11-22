-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_Measure_compProd_compProd
-- name    : ProbabilityTheory.Kernel.Measure.compProd_compProd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:48:32.51472+00:00
-- url     : https://prove2.me/theorems/51d19c48-a689-463f-8c11-537e0bad1b0f
-- title:
--   Measure: comp Prod comp Prod
-- statement:
--   The Measure construction uses the comp Prod comp Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L92-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L92-L95

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

theorem ProbabilityTheory.Kernel.Measure.compProd_compProd (μ : Measure T)
    (ξ : Kernel T S) (κ : Kernel (T × S) U) :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).map MeasurableEquiv.prodAssoc := by sorry
