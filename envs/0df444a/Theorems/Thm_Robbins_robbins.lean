-- Prove2me | Theorems.Thm_Robbins_robbins
-- name    : Robbins.robbins
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:26:00.524919+00:00
-- url     : https://prove2.me/theorems/00894de5-c709-4eb0-8086-340663c6c858
-- title:
--   Robbins: robbins
-- statement:
--   **Robbins' theorem (1939).** A finite connected graph has a strongly connected orientation if
--   and only if no edge of it is a bridge.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/Robbins.lean#L35-L90
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/Robbins.lean#L35-L90

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux
public import Definitions.Def_RobbinsLib_Robbins
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Robbins

theorem Robbins.robbins {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.Connected) :
    (∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
        ∀ u v, Relation.ReflTransGen D.Adj u v) ↔
      ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by sorry
