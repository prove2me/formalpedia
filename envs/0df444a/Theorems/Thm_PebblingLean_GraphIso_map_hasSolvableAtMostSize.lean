-- Prove2me | Theorems.Thm_PebblingLean_GraphIso_map_hasSolvableAtMostSize
-- name    : PebblingLean.GraphIso.map_hasSolvableAtMostSize
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:17.937647+00:00
-- url     : https://prove2.me/theorems/77278ea2-f448-4f75-a66c-5a350c904149
-- title:
--   Graph Iso: map has Solvable At Most Size
-- statement:
--   The Graph Iso construction uses the map has Solvable At Most Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L123-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L123-L129

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

theorem PebblingLean.GraphIso.map_hasSolvableAtMostSize [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {T k : ℕ}
    (h : Pebbling.HasSolvableAtMostSize G T k) :
    Pebbling.HasSolvableAtMostSize H T k := by sorry
