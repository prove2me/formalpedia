-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd__98091065f734
-- name    : P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd__98091065f734
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:43.676771+00:00
-- url     : https://prove2.me/theorems/cd7a99db-3bd3-4773-88ae-1d8d6024f3bf
-- title:
--   P2 M Probability Theory Kernel Measure comp Prod comp Prod  98091065f734: P2 M Probability Theory Kernel Measure comp Prod comp Prod  98091065f734
-- statement:
--   The P2 M Probability Theory Kernel Measure comp Prod comp Prod  98091065f734 construction uses the P2 M Probability Theory Kernel Measure comp Prod comp Prod  98091065f734 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L97-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L97-L101

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

theorem P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd__98091065f734 (μ : Measure T)
    (ξ : Kernel T S) (κ : Kernel (T × S) U) :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).comap
      (MeasurableEquiv.prodAssoc.symm : T × S × U ≃ᵐ (T × S) × U) := by sorry

alias «ProbabilityTheory».«Kernel».«Measure».«compProd_compProd'» := P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd__98091065f734
