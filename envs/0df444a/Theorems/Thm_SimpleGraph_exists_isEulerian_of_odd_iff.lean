-- Prove2me | Theorems.Thm_SimpleGraph_exists_isEulerian_of_odd_iff
-- name    : SimpleGraph.exists_isEulerian_of_odd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:34:31.795042+00:00
-- url     : https://prove2.me/theorems/81e528d0-b6f3-4162-bd8d-f9add31ef3a3
-- title:
--   Simple Graph: exists is Eulerian of odd iff
-- statement:
--   Versión con extremos explícitos: si los únicos vértices de grado impar son `a ≠ b`, hay un
--   trail euleriano de `a` a `b`.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L200-L204
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L200-L204

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.exists_isEulerian_of_odd_iff (hconn : G.Connected) {a b : V} (hab : a ≠ b)
    (hodd : ∀ x, Odd (G.degree x) ↔ x = a ∨ x = b) : ∃ p : G.Walk a b, p.IsEulerian := by sorry
