-- Prove2me | Theorems.Thm_SimpleGraph_exists_isEulerian_walk_iff
-- name    : SimpleGraph.exists_isEulerian_walk_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:34:37.774909+00:00
-- url     : https://prove2.me/theorems/5d0d5b93-1f88-4534-872d-adbff846efc6
-- title:
--   Simple Graph: exists is Eulerian walk iff
-- statement:
--   **Teorema de Euler (trails).** Un grafo finito conexo admite un trail euleriano si y sólo
--   si tiene 0 ó 2 vértices de grado impar.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L177-L196
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L177-L196

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.exists_isEulerian_walk_iff (hconn : G.Connected) :
    (∃ u v, ∃ p : G.Walk u v, p.IsEulerian) ↔
      Fintype.card {v | Odd (G.degree v)} = 0 ∨ Fintype.card {v | Odd (G.degree v)} = 2 := by sorry
