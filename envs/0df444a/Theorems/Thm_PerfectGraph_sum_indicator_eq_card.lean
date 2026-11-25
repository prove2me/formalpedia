-- Prove2me | Theorems.Thm_PerfectGraph_sum_indicator_eq_card
-- name    : PerfectGraph.sum_indicator_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:30:38.113239+00:00
-- url     : https://prove2.me/theorems/e11b9333-50a8-5873-9200-b7decce555e0
-- title:
--   Perfect Graph: sum indicator eq card
-- statement:
--   The Perfect Graph construction uses the sum indicator eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L117-L123
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L117-L123

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.sum_indicator_eq_card {S X : Finset V} (hX : X ⊆ S) [DecidablePred (· ∈ X)] :
    ∑ u : S, (if (u : V) ∈ X then (1 : ℚ) else 0) = X.card := by sorry
