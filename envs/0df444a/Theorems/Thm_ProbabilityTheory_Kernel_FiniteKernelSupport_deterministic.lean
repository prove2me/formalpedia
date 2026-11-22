-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_FiniteKernelSupport_deterministic
-- name    : ProbabilityTheory.Kernel.FiniteKernelSupport.deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:31:20.236307+00:00
-- url     : https://prove2.me/theorems/2885e18c-3ef1-4035-9ff6-681dd51f8559
-- title:
--   Finite Kernel Support: deterministic
-- statement:
--   Deterministic kernels have finite kernel support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L730-L737
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L730-L737

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
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

theorem ProbabilityTheory.Kernel.FiniteKernelSupport.deterministic [Countable S] [Countable T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (f : T × S → U) :
    FiniteKernelSupport (deterministic f .of_discrete) := by sorry
