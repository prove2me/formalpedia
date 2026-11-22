-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_measureReal_preimage
-- name    : ProbabilityTheory.IsUniform.measureReal_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:31.315515+00:00
-- url     : https://prove2.me/theorems/ecbe4364-caae-4018-a69d-b0e79fc76706
-- title:
--   Is Uniform: measure Real preimage
-- statement:
--   $\mathbb{P}(U_H \in H') = \dfrac{|H' \cap H|}{|H|}$
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L209-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L209-L213

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem ProbabilityTheory.IsUniform.measureReal_preimage
    {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    (H' : Set S) :
    μ.real (X ⁻¹' H') = (μ.real univ) * (Nat.card (H' ∩ H).Elem) / Nat.card H := by sorry
