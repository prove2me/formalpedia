-- Prove2me | Theorems.Thm_SimpleGraph_exists_mem_support_adj_not_mem_edges
-- name    : SimpleGraph.exists_mem_support_adj_not_mem_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:29:43.038022+00:00
-- url     : https://prove2.me/theorems/fc937a24-39ce-4a78-b8e1-486b0b441449
-- title:
--   Simple Graph: exists mem support adj not mem edges
-- statement:
--   En un grafo conexo, si un trail no es euleriano, algún vértice del trail tiene
--   una arista que el trail no usa.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L65-L82
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L65-L82

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

theorem SimpleGraph.exists_mem_support_adj_not_mem_edges (hconn : G.Connected) {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) (hne : ¬ p.IsEulerian) :
    ∃ x ∈ p.support, ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by sorry
