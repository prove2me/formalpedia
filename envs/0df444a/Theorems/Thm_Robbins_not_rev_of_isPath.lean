-- Prove2me | Theorems.Thm_Robbins_not_rev_of_isPath
-- name    : Robbins.not_rev_of_isPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:18.153494+00:00
-- url     : https://prove2.me/theorems/a1266a6a-2864-5974-983a-d206489fc95b
-- title:
--   Robbins: not rev of is Path
-- statement:
--   Two darts of a path are never reverse to each other.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L53-L63
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L53-L63

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

theorem Robbins.not_rev_of_isPath {H : SimpleGraph V} {a b : V} {q : H.Walk a b} (hq : q.IsPath)
    {d₁ d₂ : H.Dart} (h₁ : d₁ ∈ q.darts) (h₂ : d₂ ∈ q.darts) (hf : d₁.fst = d₂.snd)
    (hs : d₁.snd = d₂.fst) : False := by sorry
