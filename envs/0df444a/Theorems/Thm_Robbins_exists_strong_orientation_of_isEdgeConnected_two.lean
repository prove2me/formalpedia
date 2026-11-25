-- Prove2me | Theorems.Thm_Robbins_exists_strong_orientation_of_isEdgeConnected_two
-- name    : Robbins.exists_strong_orientation_of_isEdgeConnected_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:25:45.462637+00:00
-- url     : https://prove2.me/theorems/c239370d-3acf-5901-9470-6757d6de843b
-- title:
--   Robbins: exists strong orientation of is Edge Connected two
-- statement:
--   Every finite `2`-edge-connected graph on a nonempty vertex type has a strongly connected
--   orientation.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/Robbins.lean#L94-L103
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/Robbins.lean#L94-L103

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux
public import Definitions.Def_RobbinsLib_Robbins
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Robbins

theorem Robbins.exists_strong_orientation_of_isEdgeConnected_two {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsEdgeConnected 2) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ u v, Relation.ReflTransGen D.Adj u v := by sorry
