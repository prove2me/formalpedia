-- Prove2me | Theorems.Thm_Robbins_exists_full
-- name    : Robbins.exists_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:25.089927+00:00
-- url     : https://prove2.me/theorems/ca3d9b33-08c0-5374-9859-05c97cdf4569
-- title:
--   Robbins: exists full
-- statement:
--   A finite bridgeless graph has a partial orientation, with every arc on a directed closed walk,
--   that orients every edge.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L137-L164
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L137-L164

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Robbins
variable {V : Type*} (G : SimpleGraph V)
variable {G}
open Classical

theorem Robbins.exists_full [Finite V] (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ D : V → V → Prop, Inv G D ∧ ∀ a b, G.Adj a b → D a b ∨ D b a := by sorry
