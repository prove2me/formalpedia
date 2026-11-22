-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_entropy_condKernel_compProd_triple
-- name    : ProbabilityTheory.Kernel.entropy_condKernel_compProd_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:49:10.771363+00:00
-- url     : https://prove2.me/theorems/f6ab69a9-6f27-4bdb-8721-607e06fb9073
-- title:
--   Kernel: entropy cond Kernel comp Prod triple
-- statement:
--   The Kernel construction uses the entropy cond Kernel comp Prod triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L266-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean#L266-L272

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
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]

theorem ProbabilityTheory.Kernel.entropy_condKernel_compProd_triple
    [Nonempty V] (ξ : Kernel T S) [IsZeroOrMarkovKernel ξ]
    (κ : Kernel (T × S) U) [IsMarkovKernel κ] (η : Kernel (T × S × U) V) [IsMarkovKernel η]
    (μ : Measure T) :
    Hk[condKernel (ξ ⊗ₖ κ ⊗ₖ η) , μ ⊗ₘ (ξ ⊗ₖ κ)] = Hk[η,
      μ ⊗ₘ (ξ ⊗ₖ κ)] := by sorry
