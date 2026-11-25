-- Prove2me | Theorems.Thm_SimpleGraph_card_filter_toFinset_of_nodup
-- name    : SimpleGraph.card_filter_toFinset_of_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:52.015489+00:00
-- url     : https://prove2.me/theorems/19f39c7f-d663-4b00-b56e-24de9c69c7f5
-- title:
--   Simple Graph: card filter to Finset of nodup
-- statement:
--   The Simple Graph construction uses the card filter to Finset of nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L61-L66
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L61-L66

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.card_filter_toFinset_of_nodup {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (p : α → Prop) [DecidablePred p] : (l.toFinset.filter p).card = l.countP p := by sorry
