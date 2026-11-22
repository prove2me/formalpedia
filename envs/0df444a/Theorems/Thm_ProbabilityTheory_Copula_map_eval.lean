-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_map_eval
-- name    : ProbabilityTheory.Copula.map_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:50.410811+00:00
-- url     : https://prove2.me/theorems/90bc06ee-23e0-4675-af84-5f4d698802d7
-- title:
--   Copula: map eval
-- statement:
--   The Copula construction uses the map eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L57-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L57-L59

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

theorem ProbabilityTheory.Copula.map_eval (C : Copula d) (i : Fin d) :
    C.toMeasure.map (fun x => x i) = volume := by sorry
