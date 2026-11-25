-- Prove2me | Theorems.Thm_SimpleGraph_countP_eq_degree_of_forall_adj_mem
-- name    : SimpleGraph.countP_eq_degree_of_forall_adj_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:33:58.550526+00:00
-- url     : https://prove2.me/theorems/717edf8e-3d21-5ac8-b2b8-7afae19ca1ca
-- title:
--   Simple Graph: count P eq degree of forall adj mem
-- statement:
--   Si una lista sin repeticiones de aristas contiene todas las aristas en `x`, el número de
--   sus aristas incidentes en `x` es `deg x`.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L43-L57
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L43-L57

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.countP_eq_degree_of_forall_adj_mem {L : List (Sym2 V)} (hL : L.Nodup)
    (hsub : ∀ e ∈ L, e ∈ G.edgeSet) {x : V} (h : ∀ y, G.Adj x y → s(x, y) ∈ L) :
    L.countP (fun e => x ∈ e) = G.degree x := by sorry
