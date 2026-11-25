-- Prove2me | Theorems.Thm_SimpleGraph_exists_isEulerian_circuit_at
-- name    : SimpleGraph.exists_isEulerian_circuit_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:34:01.623116+00:00
-- url     : https://prove2.me/theorems/ea08feb6-896a-4dfe-a380-aca951662da5
-- title:
--   Simple Graph: exists is Eulerian circuit at
-- statement:
--   En un grafo conexo con todos los grados pares hay un circuito euleriano que pasa por
--   cualquier vértice prefijado.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L171-L173
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L171-L173

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.exists_isEulerian_circuit_at (hconn : G.Connected) (heven : ∀ v, Even (G.degree v))
    (a : V) : ∃ p : G.Walk a a, p.IsEulerian := by sorry
