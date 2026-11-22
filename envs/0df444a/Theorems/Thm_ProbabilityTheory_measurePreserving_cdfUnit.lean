-- Prove2me | Theorems.Thm_ProbabilityTheory_measurePreserving_cdfUnit
-- name    : ProbabilityTheory.measurePreserving_cdfUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:13.377733+00:00
-- url     : https://prove2.me/theorems/31694f82-e8c4-428e-b963-1f81884320b9
-- title:
--   Probability Theory: measure Preserving cdf Unit
-- statement:
--   The CDF transform is measure preserving when its CDF is continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L100-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L100-L102

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

theorem ProbabilityTheory.measurePreserving_cdfUnit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) : MeasurePreserving (cdfUnit μ) μ volume := by sorry
