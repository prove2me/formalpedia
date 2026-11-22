-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_sum_meas_smul_cond_fiber__96388389e218
-- name    : P2M_ProbabilityTheory_sum_meas_smul_cond_fiber__96388389e218
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:20.575253+00:00
-- url     : https://prove2.me/theorems/7704f351-8d35-4725-bafc-2e539daa798d
-- title:
--   P2 M Probability Theory sum meas smul cond fiber  96388389e218: P2 M Probability Theory sum meas smul cond fiber  96388389e218
-- statement:
--   The **law of total probability** for a random variable taking finitely many values:
--   a measure
--   `μ` can be expressed as a linear combination of its conditional measures `μ[|X ← x]` on
--   fibers of a
--   random variable `X` valued in a fintype.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/ConditionalProbability.lean#L33-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/ConditionalProbability.lean#L33-L45

module
public import Mathlib.Probability.ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open ProbabilityTheory
variable {Ω α : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
 [MeasurableSpace α] [MeasurableSingletonClass α]

theorem P2M_ProbabilityTheory_sum_meas_smul_cond_fiber__96388389e218 {X : Ω → α} (hX : Measurable X) [finX : FiniteRange X]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x ∈ finX.toFinset, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by sorry

alias «ProbabilityTheory».«sum_meas_smul_cond_fiber'» := P2M_ProbabilityTheory_sum_meas_smul_cond_fiber__96388389e218
