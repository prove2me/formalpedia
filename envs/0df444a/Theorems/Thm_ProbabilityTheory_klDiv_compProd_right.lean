-- Prove2me | Theorems.Thm_ProbabilityTheory_klDiv_compProd_right
-- name    : ProbabilityTheory.klDiv_compProd_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:39.465303+00:00
-- url     : https://prove2.me/theorems/b1b8fc4c-1095-48c0-9b24-98e25bbc3dcc
-- title:
--   Probability Theory: kl Div comp Prod right
-- statement:
--   The Kullback-Leibler divergence of `μ ⊗ₘ κ` with respect to `μ ⊗ₘ η` is the integral of the
--   pointwise kernel divergences.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/KernelCompositionKullbackLeibler.lean#L104-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/KernelCompositionKullbackLeibler.lean#L104-L137

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

theorem ProbabilityTheory.klDiv_compProd_right
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by sorry
