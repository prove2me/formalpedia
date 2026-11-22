-- Prove2me | Theorems.Thm_ProbabilityTheory_coe_cdfUnit
-- name    : ProbabilityTheory.coe_cdfUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:56.086707+00:00
-- url     : https://prove2.me/theorems/8588aac4-ec1c-406a-8326-7f84df18ddd0
-- title:
--   Probability Theory: coe cdf Unit
-- statement:
--   The Probability Theory construction uses the coe cdf Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L30-L30
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean#L30-L30

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

theorem ProbabilityTheory.coe_cdfUnit (μ : Measure ℝ) (x : ℝ) : (cdfUnit μ x : ℝ) = cdf μ x := by sorry

attribute [defeq] ProbabilityTheory.coe_cdfUnit
