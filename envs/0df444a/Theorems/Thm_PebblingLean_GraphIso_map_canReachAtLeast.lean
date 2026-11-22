-- Prove2me | Theorems.Thm_PebblingLean_GraphIso_map_canReachAtLeast
-- name    : PebblingLean.GraphIso.map_canReachAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:54.736776+00:00
-- url     : https://prove2.me/theorems/e3d9f226-a7dc-472a-89f3-d17975990dd4
-- title:
--   Graph Iso: map can Reach At Least
-- statement:
--   The Graph Iso construction uses the map can Reach At Least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L102-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L102-L108

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

theorem PebblingLean.GraphIso.map_canReachAtLeast [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D : Pebbling V} {target : W} {T : ℕ}
    (hcan : Pebbling.CanReachAtLeast G D (iso.toEquiv.symm target) T) :
    Pebbling.CanReachAtLeast H (iso.mapDistribution D) target T := by sorry
