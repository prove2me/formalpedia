-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_condKernel_compProd_apply__368aa807565a
-- name    : P2M_ProbabilityTheory_Kernel_condKernel_compProd_apply__368aa807565a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:36:12.460377+00:00
-- url     : https://prove2.me/theorems/88c14160-be58-46ef-a9ce-51c91ac9d34f
-- title:
--   P2 M Probability Theory Kernel cond Kernel comp Prod apply  368aa807565a: P2 M Probability Theory Kernel cond Kernel comp Prod apply  368aa807565a
-- statement:
--   The P2 M Probability Theory Kernel cond Kernel comp Prod apply  368aa807565a construction uses the P2 M Probability Theory Kernel cond Kernel comp Prod apply  368aa807565a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L67-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L67-L80

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

theorem P2M_ProbabilityTheory_Kernel_condKernel_compProd_apply__368aa807565a (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) {s : Set U} (hs : MeasurableSet s) :
    condKernel (κ ⊗ₖ η) x s = η x s := by sorry

alias «ProbabilityTheory».«Kernel».«condKernel_compProd_apply'» := P2M_ProbabilityTheory_Kernel_condKernel_compProd_apply__368aa807565a
