-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_submodular_compProd
-- name    : ProbabilityTheory.Kernel.entropy_submodular_compProd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:26.483596+00:00
-- url     : https://prove2.me/theorems/9191f903-ace6-420b-8182-e83e67b7531f
-- title:
--   Kernel: entropy submodular comp Prod
-- statement:
--   The Kernel construction uses the entropy submodular comp Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L276-L317
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L276-L317

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
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]

theorem ProbabilityTheory.Kernel.entropy_submodular_compProd
    {ξ : Kernel T S} [IsZeroOrMarkovKernel ξ]
    {κ : Kernel (T × S) U} [IsZeroOrMarkovKernel κ] {η :
      Kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ :
      AEFiniteKernelSupport ξ μ) :
    Hk[η, μ ⊗ₘ (ξ ⊗ₖ κ)]
      ≤ Hk[snd (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc
        MeasurableEquiv.prodAssoc.measurable)),
            μ ⊗ₘ ξ] := by sorry
