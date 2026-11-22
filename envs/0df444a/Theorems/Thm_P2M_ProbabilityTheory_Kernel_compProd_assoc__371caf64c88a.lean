-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_compProd_assoc__371caf64c88a
-- name    : P2M_ProbabilityTheory_Kernel_compProd_assoc__371caf64c88a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:48:48.550871+00:00
-- url     : https://prove2.me/theorems/aaf4c7e7-85cf-47a3-b45f-197f5d06274c
-- title:
--   P2 M Probability Theory Kernel comp Prod assoc  371caf64c88a: P2 M Probability Theory Kernel comp Prod assoc  371caf64c88a
-- statement:
--   The P2 M Probability Theory Kernel comp Prod assoc  371caf64c88a construction uses the P2 M Probability Theory Kernel comp Prod assoc  371caf64c88a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L76-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L76-L90

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

theorem P2M_ProbabilityTheory_Kernel_compProd_assoc__371caf64c88a (ξ : Kernel T S) [IsSFiniteKernel ξ]
    (κ : Kernel (T × S) U) [IsSFiniteKernel κ] (η :
      Kernel (T × S × U) V) [IsSFiniteKernel η] :
    map ((ξ ⊗ₖ κ) ⊗ₖ η) MeasurableEquiv.prodAssoc
      = ξ ⊗ₖ
        (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)) := by sorry

alias «ProbabilityTheory».«Kernel».«compProd_assoc'» := P2M_ProbabilityTheory_Kernel_compProd_assoc__371caf64c88a
