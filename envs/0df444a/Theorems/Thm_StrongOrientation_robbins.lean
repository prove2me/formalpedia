-- Prove2me | Theorems.Thm_StrongOrientation_robbins
-- name    : StrongOrientation.robbins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:39:34.258842+00:00
-- url     : https://prove2.me/theorems/53598091-3bd5-4ed7-9b78-45254dc48392
-- title:
--   Strong Orientation: robbins
-- statement:
--   **Robbins' theorem (1939).** A finite connected graph has a strongly connected orientation if
--   and only if no edge of it is a bridge.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/Solution.lean#L31-L35
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/Solution.lean#L31-L35

module
public import Mathlib
public import Definitions.Def_RobbinsLib_Robbins
public import Definitions.Def_RobbinsStrongOrientation_Solution
public import Theorems.Thm_Robbins_robbins

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open StrongOrientation

theorem StrongOrientation.robbins {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    (∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
        ∀ u v, Relation.ReflTransGen D.Adj u v) ↔
      ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by sorry
