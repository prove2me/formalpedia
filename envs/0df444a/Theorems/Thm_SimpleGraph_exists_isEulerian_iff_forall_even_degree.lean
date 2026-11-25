-- Prove2me | Theorems.Thm_SimpleGraph_exists_isEulerian_iff_forall_even_degree
-- name    : SimpleGraph.exists_isEulerian_iff_forall_even_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:29:58.454185+00:00
-- url     : https://prove2.me/theorems/18c9fd18-4d17-5c1a-b44e-9b0279b8d675
-- title:
--   Simple Graph: exists is Eulerian iff forall even degree
-- statement:
--   **Teorema de Euler.** Un grafo finito conexo admite un circuito euleriano si y sólo si
--   todos sus vértices tienen grado par.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L138-L143
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L138-L143

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

theorem SimpleGraph.exists_isEulerian_iff_forall_even_degree (hconn : G.Connected) :
    (∃ u, ∃ p : G.Walk u u, p.IsEulerian) ↔ ∀ v, Even (G.degree v) := by sorry
