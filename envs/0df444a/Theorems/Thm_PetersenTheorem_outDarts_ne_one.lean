-- Prove2me | Theorems.Thm_PetersenTheorem_outDarts_ne_one
-- name    : PetersenTheorem.outDarts_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:43.920413+00:00
-- url     : https://prove2.me/theorems/2953e328-15e2-40c5-a9af-269fdae2085e
-- title:
--   Petersen Theorem: out Darts ne one
-- statement:
--   The Petersen Theorem construction uses the out Darts ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L74-L97
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L74-L97

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

theorem PetersenTheorem.outDarts_ne_one (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (C : Finset V) :
    outDarts G C ≠ 1 := by sorry
