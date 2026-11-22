-- Prove2me | Theorems.Thm_ProbabilityTheory_IsUniform_restrict
-- name    : ProbabilityTheory.IsUniform.restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:38.060124+00:00
-- url     : https://prove2.me/theorems/b9c28474-0c95-4bb3-8540-75f997c6bb22
-- title:
--   Is Uniform: restrict
-- statement:
--   If $X$ is uniform w.r.t. $\mu$ on $H$, then $X$ is uniform w.r.t. $\mu$ conditioned
--   by
--   $H'$ on $H' \cap H$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L257-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Uniform.lean#L257-L277

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

theorem ProbabilityTheory.IsUniform.restrict
    {H : Set S} (h : IsUniform H X μ) (hX : Measurable X) (H' : Set S) :
    IsUniform (H' ∩ H) X (μ[|X ⁻¹' H']) := by sorry
