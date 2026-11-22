-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage
-- name    : ProbabilityTheory.IsUniform.measure_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:24.818348+00:00
-- url     : https://prove2.me/theorems/ee1025bc-4c17-4b60-92f7-9936e322d2b9
-- title:
--   Is Uniform: measure preimage
-- statement:
--   $\mathbb{P}(U_H \in H') = \dfrac{|H' \cap H|}{|H|}$
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L191-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L191-L206

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

theorem ProbabilityTheory.IsUniform.measure_preimage
    {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    (H' : Set S) : μ (X ⁻¹' H') = (μ univ) * (Nat.card (H' ∩ H : Set S)) / Nat.card H := by sorry
