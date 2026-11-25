-- Prove2me | Theorems.Thm_SimpleGraph_exists_adj_not_mem_of_countP_ne
-- name    : SimpleGraph.exists_adj_not_mem_of_countP_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:34:32.976007+00:00
-- url     : https://prove2.me/theorems/bf09dca9-8f15-4b28-993e-da123ae1077f
-- title:
--   Simple Graph: exists adj not mem of count P ne
-- statement:
--   Si una lista sin repeticiones de aristas no tiene `deg x` aristas en `x`, falta alguna
--   arista en `x`.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L61-L65
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L61-L65

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.exists_adj_not_mem_of_countP_ne {L : List (Sym2 V)} (hL : L.Nodup)
    (hsub : ∀ e ∈ L, e ∈ G.edgeSet) {x : V} (h : L.countP (fun e => x ∈ e) ≠ G.degree x) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ L := by sorry
