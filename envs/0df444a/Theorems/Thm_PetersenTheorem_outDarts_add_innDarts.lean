-- Prove2me | Theorems.Thm_PetersenTheorem_outDarts_add_innDarts
-- name    : PetersenTheorem.outDarts_add_innDarts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:36.232593+00:00
-- url     : https://prove2.me/theorems/d60411e8-95a9-4ee7-b290-3d5a98314145
-- title:
--   Petersen Theorem: out Darts add inn Darts
-- statement:
--   The Petersen Theorem construction uses the out Darts add inn Darts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L66-L72
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L66-L72

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

theorem PetersenTheorem.outDarts_add_innDarts (h3 : G.IsRegularOfDegree 3) (C : Finset V) :
    outDarts G C + innDarts G C = 3 * C.card := by sorry
