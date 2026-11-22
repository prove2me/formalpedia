-- Prove2me | Theorems.Thm_PebblingLean_GraphIso_map_move
-- name    : PebblingLean.GraphIso.map_move
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:13.12962+00:00
-- url     : https://prove2.me/theorems/55f52ba6-e7c7-4bd1-a0f8-cb83cff5e8f5
-- title:
--   Graph Iso: map move
-- statement:
--   The Graph Iso construction uses the map move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L59-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L59-L90

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}

theorem PebblingLean.GraphIso.map_move [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D E : Pebbling V}
    (hmove : Pebbling.Move G D E) :
    Pebbling.Move H (iso.mapDistribution D) (iso.mapDistribution E) := by sorry
