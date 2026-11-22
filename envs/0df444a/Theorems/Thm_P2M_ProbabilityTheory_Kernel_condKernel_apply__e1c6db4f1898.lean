-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
-- name    : P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:31:26.067+00:00
-- url     : https://prove2.me/theorems/7b7d89e5-aff1-4ce2-bc0a-a207b1e112b6
-- title:
--   P2 M Probability Theory Kernel cond Kernel apply  e1c6db4f1898: P2 M Probability Theory Kernel cond Kernel apply  e1c6db4f1898
-- statement:
--   The P2 M Probability Theory Kernel cond Kernel apply  e1c6db4f1898 construction uses the P2 M Probability Theory Kernel cond Kernel apply  e1c6db4f1898 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L59-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L59-L65

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

theorem P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898 (κ : Kernel T (S × U)) [IsFiniteKernel κ]
    (x : T × S) (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) (s : Set U) :
    condKernel κ x s
      = (κ x.1 (Prod.fst ⁻¹' {x.2}))⁻¹ * (κ x.1) ({x.2} ×ˢ s) := by sorry

alias «ProbabilityTheory».«Kernel».«condKernel_apply'» := P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
