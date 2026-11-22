-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_toMeasure_injective
-- name    : ProbabilityTheory.Copula.toMeasure_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:58.225385+00:00
-- url     : https://prove2.me/theorems/0e265e1f-9325-4b48-b2d7-d787d5f96eb8
-- title:
--   Copula: to Measure injective
-- statement:
--   The Copula construction uses the to Measure injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L53-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L53-L54

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.toMeasure_injective : Function.Injective (toMeasure (d := d)) := by sorry
