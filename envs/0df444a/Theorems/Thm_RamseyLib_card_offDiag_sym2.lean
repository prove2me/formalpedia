-- Prove2me | Theorems.Thm_RamseyLib_card_offDiag_sym2
-- name    : RamseyLib.card_offDiag_sym2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:55.437793+00:00
-- url     : https://prove2.me/theorems/ce1f9b4e-26d4-47c9-8c8b-71354bdc08c6
-- title:
--   Ramsey Lib: card off Diag sym2
-- statement:
--   The Ramsey Lib construction uses the card off Diag sym2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L113-L129
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L113-L129

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.card_offDiag_sym2 {α : Type*} [DecidableEq α] (S : Finset α) :
    (S.sym2.filter (fun e => ¬ e.IsDiag)).card = S.card.choose 2 := by sorry
