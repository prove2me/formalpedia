-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_triple_add_entropy_le
-- name    : ProbabilityTheory.Kernel.entropy_compProd_triple_add_entropy_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:21.584919+00:00
-- url     : https://prove2.me/theorems/8f577f02-bc9c-4d7e-aae3-7fd79df040c0
-- title:
--   Kernel: entropy comp Prod triple add entropy le
-- statement:
--   The Kernel construction uses the entropy comp Prod triple add entropy le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L320-L361
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L320-L361

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

theorem ProbabilityTheory.Kernel.entropy_compProd_triple_add_entropy_le
    {ξ : Kernel T S} [IsZeroOrMarkovKernel ξ]
    {κ : Kernel (T × S) U} [IsMarkovKernel κ]
    {η : Kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ :
      AEFiniteKernelSupport ξ μ) :
    Hk[(ξ ⊗ₖ κ) ⊗ₖ η, μ] + Hk[ξ, μ]
      ≤ Hk[ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc
        MeasurableEquiv.prodAssoc.measurable),
          μ] + Hk[ξ ⊗ₖ κ, μ] := by sorry
