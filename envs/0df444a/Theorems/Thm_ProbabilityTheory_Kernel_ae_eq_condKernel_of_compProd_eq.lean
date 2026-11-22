-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_ae_eq_condKernel_of_compProd_eq
-- name    : ProbabilityTheory.Kernel.ae_eq_condKernel_of_compProd_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:37:52.033172+00:00
-- url     : https://prove2.me/theorems/d6210d66-1496-4cb1-bce1-8903b11d1a1a
-- title:
--   Kernel: ae eq cond Kernel of comp Prod eq
-- statement:
--   The Kernel construction uses the ae eq cond Kernel of comp Prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L151-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L151-L156

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
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]
open ProbabilityTheory.Kernel
variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]
variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]

theorem ProbabilityTheory.Kernel.ae_eq_condKernel_of_compProd_eq (κ : Kernel T (S × U)) [IsFiniteKernel κ] {μ}
    (η : Kernel (T × S) U) [IsMarkovKernel η] (h : fst κ ⊗ₖ η = κ) :
    η =ᵐ[μ ⊗ₘ fst κ] condKernel κ := by sorry
