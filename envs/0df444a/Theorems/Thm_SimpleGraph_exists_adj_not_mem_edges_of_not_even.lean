-- Prove2me | Theorems.Thm_SimpleGraph_exists_adj_not_mem_edges_of_not_even
-- name    : SimpleGraph.exists_adj_not_mem_edges_of_not_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:00.291682+00:00
-- url     : https://prove2.me/theorems/e334a060-15d0-4017-ba19-080931129088
-- title:
--   Simple Graph: exists adj not mem edges of not even
-- statement:
--   Si el número de aristas de un trail incidentes en `x` no tiene la paridad de `deg x`,
--   hay una arista en `x` que el trail no usa.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L42-L61
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L42-L61

module
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Euler_Basic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.exists_adj_not_mem_edges_of_not_even {u v x : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hx : Even (G.degree x)) (hodd : ¬ Even (p.edges.countP fun e => x ∈ e)) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by sorry
