-- Prove2me | Theorems.Thm_PetersenTheorem_three_le_outDarts
-- name    : PetersenTheorem.three_le_outDarts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:26.741438+00:00
-- url     : https://prove2.me/theorems/4eb97a27-53b3-5cc3-8b42-801171439fbc
-- title:
--   Petersen Theorem: three le out Darts
-- statement:
--   The Petersen Theorem construction uses the three le out Darts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L99-L106
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L99-L106

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem PetersenTheorem.three_le_outDarts (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (C : Finset V) (hC : Odd C.card) : 3 ≤ outDarts G C := by sorry
