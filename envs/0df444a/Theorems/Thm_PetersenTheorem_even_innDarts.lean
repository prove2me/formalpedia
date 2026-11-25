-- Prove2me | Theorems.Thm_PetersenTheorem_even_innDarts
-- name    : PetersenTheorem.even_innDarts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:38.616585+00:00
-- url     : https://prove2.me/theorems/59836c18-cbd6-4500-881d-dcbf0d684bc0
-- title:
--   Petersen Theorem: even inn Darts
-- statement:
--   The Petersen Theorem construction uses the even inn Darts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L43-L64
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L43-L64

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

theorem PetersenTheorem.even_innDarts (C : Finset V) : Even (innDarts G C) := by sorry
