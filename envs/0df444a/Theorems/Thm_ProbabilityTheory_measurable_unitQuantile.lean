-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_unitQuantile
-- name    : ProbabilityTheory.measurable_unitQuantile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:58.183652+00:00
-- url     : https://prove2.me/theorems/20cf23fa-1106-4f7c-b811-9dbf5c866e89
-- title:
--   Probability Theory: measurable unit Quantile
-- statement:
--   The Probability Theory construction uses the measurable unit Quantile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/Quantile.lean#L34-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/Quantile.lean#L34-L35

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

theorem ProbabilityTheory.measurable_unitQuantile (μ : Measure I) : Measurable (unitQuantile μ) := by sorry
