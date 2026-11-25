-- Prove2me | Theorems.Thm_Robbins_reach_of_walk
-- name    : Robbins.reach_of_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:26.427006+00:00
-- url     : https://prove2.me/theorems/40279511-d08e-46dd-a6ba-8dae02b39793
-- title:
--   Robbins: reach of walk
-- statement:
--   Chaining reachability along the darts of a walk.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L44-L50
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L44-L50

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

theorem Robbins.reach_of_walk {H : SimpleGraph V} {D : V → V → Prop} :
    ∀ {a b : V} (p : H.Walk a b), (∀ d ∈ p.darts, Relation.ReflTransGen D d.fst d.snd) →
      Relation.ReflTransGen D a b
  := by sorry
