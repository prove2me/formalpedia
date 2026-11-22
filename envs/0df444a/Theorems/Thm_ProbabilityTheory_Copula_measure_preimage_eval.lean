-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_measure_preimage_eval
-- name    : ProbabilityTheory.Copula.measure_preimage_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:57.064176+00:00
-- url     : https://prove2.me/theorems/9311c699-12e2-440a-8253-8b89a01262fa
-- title:
--   Copula: measure preimage eval
-- statement:
--   The probability of a measurable coordinate event is its uniform volume.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L67-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L67-L69

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

theorem ProbabilityTheory.Copula.measure_preimage_eval (C : Copula d) (i : Fin d) {s : Set I}
    (hs : MeasurableSet s) : C.toMeasure ((fun x => x i) ⁻¹' s) = volume s := by sorry
