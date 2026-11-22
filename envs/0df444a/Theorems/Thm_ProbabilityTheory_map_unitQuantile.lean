-- Prove2me | Theorems.Thm_ProbabilityTheory_map_unitQuantile
-- name    : ProbabilityTheory.map_unitQuantile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:58.040656+00:00
-- url     : https://prove2.me/theorems/e0185b28-5613-4e0c-9498-1ff59506158a
-- title:
--   Probability Theory: map unit Quantile
-- statement:
--   Inverse-transform sampling is valid for arbitrary laws, including atomic laws.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/Quantile.lean#L74-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/Quantile.lean#L74-L84

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

theorem ProbabilityTheory.map_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ] :
    volume.map (unitQuantile μ) = μ := by sorry
