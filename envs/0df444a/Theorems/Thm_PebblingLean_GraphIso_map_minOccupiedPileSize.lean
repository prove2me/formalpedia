-- Prove2me | Theorems.Thm_PebblingLean_GraphIso_map_minOccupiedPileSize
-- name    : PebblingLean.GraphIso.map_minOccupiedPileSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:06.137082+00:00
-- url     : https://prove2.me/theorems/d6c862e4-5638-43aa-8d77-8818c8f72639
-- title:
--   Graph Iso: map min Occupied Pile Size
-- statement:
--   The Graph Iso construction uses the map min Occupied Pile Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L117-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L117-L121

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

theorem PebblingLean.GraphIso.map_minOccupiedPileSize (iso : GraphIso G H) {D : Pebbling V} {S : ℕ}
    (hmin : Pebbling.MinOccupiedPileSize D S) :
    Pebbling.MinOccupiedPileSize (iso.mapDistribution D) S := by sorry
