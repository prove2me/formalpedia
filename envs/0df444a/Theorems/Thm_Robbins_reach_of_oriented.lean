-- Prove2me | Theorems.Thm_Robbins_reach_of_oriented
-- name    : Robbins.reach_of_oriented
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:31.826596+00:00
-- url     : https://prove2.me/theorems/12c92424-a7e8-4c42-bd20-589194f4923a
-- title:
--   Robbins: reach of oriented
-- statement:
--   The Robbins construction uses the reach of oriented property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L37-L41
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L37-L41

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

theorem Robbins.reach_of_oriented {D : V → V → Prop} (h : Inv G D) {x y : V} (hxy : D x y ∨ D y x) :
    Relation.ReflTransGen D x y := by sorry
