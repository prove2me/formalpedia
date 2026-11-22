-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
-- name    : ProbabilityTheory.Copula.measure_eval_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:53.389328+00:00
-- url     : https://prove2.me/theorems/eaedd488-6f22-4958-abfc-41743dc48b51
-- title:
--   Copula: measure eval le
-- statement:
--   The Copula construction uses the measure eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L72-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L72-L74

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

theorem ProbabilityTheory.Copula.measure_eval_le (C : Copula d) (i : Fin d) (u : I) :
    C.toMeasure {x | x i ≤ u} = ENNReal.ofReal (u : ℝ) := by sorry
