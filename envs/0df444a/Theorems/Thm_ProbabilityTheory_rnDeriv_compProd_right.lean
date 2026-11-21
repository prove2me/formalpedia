-- Prove2me | Theorems.Thm_ProbabilityTheory_rnDeriv_compProd_right
-- name    : ProbabilityTheory.rnDeriv_compProd_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:41.215337+00:00
-- url     : https://prove2.me/theorems/35a0a92a-70ff-476d-8b42-cc56e1312a29
-- title:
--   Probability Theory: rn Deriv comp Prod right
-- statement:
--   The Radon-Nikodym derivative of `μ ⊗ₘ κ` with respect to `μ ⊗ₘ η` is the pointwise
--   Radon-Nikodym derivative of the kernels.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/KernelCompositionKullbackLeibler.lean#L76-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/KernelCompositionKullbackLeibler.lean#L76-L100

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ProbabilityTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem ProbabilityTheory.rnDeriv_compProd_right
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ κ.rnDeriv η p.1 p.2 := by sorry
