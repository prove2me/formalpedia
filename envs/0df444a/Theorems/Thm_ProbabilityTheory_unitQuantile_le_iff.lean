-- Prove2me | Theorems.Thm_ProbabilityTheory_unitQuantile_le_iff
-- name    : ProbabilityTheory.unitQuantile_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:58.887163+00:00
-- url     : https://prove2.me/theorems/cd11bdfa-d2e8-4cda-a6b4-3e229abdeadb
-- title:
--   Probability Theory: unit Quantile le iff
-- statement:
--   The quantile adjunction holds at atoms and at both endpoints.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/Quantile.lean#L38-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/Quantile.lean#L38-L71

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory

theorem ProbabilityTheory.unitQuantile_le_iff (μ : Measure I) [IsProbabilityMeasure μ] (t x : I) :
    unitQuantile μ t ≤ x ↔ (t : ℝ) ≤ μ.real (Iic x) := by sorry
