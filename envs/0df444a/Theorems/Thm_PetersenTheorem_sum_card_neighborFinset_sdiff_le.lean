-- Prove2me | Theorems.Thm_PetersenTheorem_sum_card_neighborFinset_sdiff_le
-- name    : PetersenTheorem.sum_card_neighborFinset_sdiff_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:57.898969+00:00
-- url     : https://prove2.me/theorems/195d55e3-6b09-46b1-927e-f520d1afd0d3
-- title:
--   Petersen Theorem: sum card neighbor Finset sdiff le
-- statement:
--   The Petersen Theorem construction uses the sum card neighbor Finset sdiff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L198-L203
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L198-L203

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}

theorem PetersenTheorem.sum_card_neighborFinset_sdiff_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) (T : Finset V) :
    ∑ y ∈ T, (G.neighborFinset y \ T).card ≤ 3 * T.card := by sorry
