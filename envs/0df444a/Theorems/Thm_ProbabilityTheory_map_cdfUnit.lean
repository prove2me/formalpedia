-- Prove2me | Theorems.Thm_ProbabilityTheory_map_cdfUnit
-- name    : ProbabilityTheory.map_cdfUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:56.485178+00:00
-- url     : https://prove2.me/theorems/bcca9c2f-cfc1-4cb4-9752-1175e45fa874
-- title:
--   Probability Theory: map cdf Unit
-- statement:
--   Applying a continuous CDF to a variable with that law gives a uniform variable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L55-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L55-L97

module
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory

theorem ProbabilityTheory.map_cdfUnit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) : μ.map (cdfUnit μ) = volume := by sorry
