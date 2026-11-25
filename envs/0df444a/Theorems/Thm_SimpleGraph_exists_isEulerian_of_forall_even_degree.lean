-- Prove2me | Theorems.Thm_SimpleGraph_exists_isEulerian_of_forall_even_degree
-- name    : SimpleGraph.exists_isEulerian_of_forall_even_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:24.354697+00:00
-- url     : https://prove2.me/theorems/887f63ba-e478-46bf-a5f6-176afce6621d
-- title:
--   Simple Graph: exists is Eulerian of forall even degree
-- statement:
--   **Euler (suficiencia).** Un grafo finito conexo con todos sus grados pares admite un
--   circuito euleriano.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L118-L134
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L118-L134

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

theorem SimpleGraph.exists_isEulerian_of_forall_even_degree (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) : ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by sorry
