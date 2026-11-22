-- Prove2me | Theorems.Thm_ProbabilityTheory_continuous_cdf_of_atomless
-- name    : ProbabilityTheory.continuous_cdf_of_atomless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:59.277625+00:00
-- url     : https://prove2.me/theorems/31482fab-418e-43c6-b0a7-0bc52cc38aeb
-- title:
--   Probability Theory: continuous cdf of atomless
-- statement:
--   An atomless real probability measure has a continuous CDF.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L43-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L43-L52

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

theorem ProbabilityTheory.continuous_cdf_of_atomless (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by sorry
