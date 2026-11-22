-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
-- name    : ProbabilityTheory.Copula.toMeasure_ofMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:50.184096+00:00
-- url     : https://prove2.me/theorems/cca57c79-bee7-4d7c-8943-c2db8f7f7d65
-- title:
--   Copula: to Measure of Map
-- statement:
--   The Copula construction uses the to Measure of Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L92-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L92-L95

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

theorem ProbabilityTheory.Copula.toMeasure_ofMap {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → Fin d → I) (hX : Measurable X)
    (hmarg : ∀ i, μ.toMeasure.map (fun ω => X ω i) = volume) :
    (ofMap μ X hX hmarg).toMeasure = μ.toMeasure.map X := by sorry

attribute [defeq] ProbabilityTheory.Copula.toMeasure_ofMap
