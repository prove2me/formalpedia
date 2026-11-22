-- Prove2me | Theorems.Thm_ProbabilityTheory_Kernel_finiteKernelSupport_of_finite_range
-- name    : ProbabilityTheory.Kernel.finiteKernelSupport_of_finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:38:45.911961+00:00
-- url     : https://prove2.me/theorems/7bd7cfe3-76f0-467f-95d4-b29bb13697ae
-- title:
--   Kernel: finite Kernel Support of finite range
-- statement:
--   Finite range implies finite kernel support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L721-L727
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Kernel/Disintegration.lean#L721-L727

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

theorem ProbabilityTheory.Kernel.finiteKernelSupport_of_finite_range
    [Finite S] (κ : Kernel T S) : FiniteKernelSupport κ := by sorry
