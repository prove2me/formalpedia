-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
-- name    : ProbabilityTheory.Copula.measureReal_eval_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:50.012094+00:00
-- url     : https://prove2.me/theorems/2ce08d4f-e4f1-4260-9011-b57b74cfecce
-- title:
--   Copula: measure Real eval le
-- statement:
--   The Copula construction uses the measure Real eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L77-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L77-L79

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

theorem ProbabilityTheory.Copula.measureReal_eval_le (C : Copula d) (i : Fin d) (u : I) :
    C.toMeasure.real {x | x i ≤ u} = (u : ℝ) := by sorry
