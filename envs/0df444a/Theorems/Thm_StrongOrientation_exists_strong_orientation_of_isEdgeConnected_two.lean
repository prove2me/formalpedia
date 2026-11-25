-- Prove2me | Theorems.Thm_StrongOrientation_exists_strong_orientation_of_isEdgeConnected_two
-- name    : StrongOrientation.exists_strong_orientation_of_isEdgeConnected_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:43:37.714237+00:00
-- url     : https://prove2.me/theorems/fa990b59-8b2d-52fb-a199-4abe833cc973
-- title:
--   Strong Orientation: exists strong orientation of is Edge Connected two
-- statement:
--   Every finite `2`-edge-connected graph on a nonempty vertex type has a strongly connected
--   orientation.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/Solution.lean#L39-L43
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/Solution.lean#L39-L43

module
public import Mathlib
public import Definitions.Def_RobbinsLib_Robbins
public import Definitions.Def_RobbinsStrongOrientation_Solution
public import Theorems.Thm_Robbins_exists_strong_orientation_of_isEdgeConnected_two

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open StrongOrientation

theorem StrongOrientation.exists_strong_orientation_of_isEdgeConnected_two {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsEdgeConnected 2) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ u v, Relation.ReflTransGen D.Adj u v := by sorry
