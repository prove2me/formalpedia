-- Prove2me | Theorems.Thm_PebblingLean_GraphIso_map_solvableAtLeast
-- name    : PebblingLean.GraphIso.map_solvableAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:59.306272+00:00
-- url     : https://prove2.me/theorems/613564e6-639a-416c-9225-e9985a0e5c2e
-- title:
--   Graph Iso: map solvable At Least
-- statement:
--   The Graph Iso construction uses the map solvable At Least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L110-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L110-L115

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

theorem PebblingLean.GraphIso.map_solvableAtLeast [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D : Pebbling V} {T : ℕ}
    (hsolv : Pebbling.SolvableAtLeast G D T) :
    Pebbling.SolvableAtLeast H (iso.mapDistribution D) T := by sorry
