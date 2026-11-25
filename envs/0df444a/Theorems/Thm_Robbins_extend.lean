-- Prove2me | Theorems.Thm_Robbins_extend
-- name    : Robbins.extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:45.919897+00:00
-- url     : https://prove2.me/theorems/eae85cc6-0f0a-4584-8827-6b3397d673f0
-- title:
--   Robbins: extend
-- statement:
--   **The ear step.** An unoriented edge `uv` that is not a bridge can be oriented, together with
--   the unoriented edges of a path from `v` to `u` avoiding `uv`, preserving the invariant.
--
--   Source: https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L68-L132
-- source:
--   https://github.com/jtraverso/robbins-strong-orientation/blob/076e734e9949720d3e4fcc2cc3cad4284871442c/RobbinsLib/RobbinsAux.lean#L68-L132

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

theorem Robbins.extend {D : V → V → Prop} (hI : Inv G D) {u v : V} (huv : G.Adj u v) (hnu : ¬ D u v)
    (hnv : ¬ D v u) (hnb : ¬ G.IsBridge s(u, v)) :
    ∃ D' : V → V → Prop, Inv G D' ∧ (∀ a b, D a b → D' a b) ∧ D' u v := by sorry
