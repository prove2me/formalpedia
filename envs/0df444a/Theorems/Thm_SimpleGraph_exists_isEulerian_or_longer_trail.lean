-- Prove2me | Theorems.Thm_SimpleGraph_exists_isEulerian_or_longer_trail
-- name    : SimpleGraph.exists_isEulerian_or_longer_trail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:07.627741+00:00
-- url     : https://prove2.me/theorems/ca1b367c-ee1f-46bc-9951-8fb2493b8609
-- title:
--   Simple Graph: exists is Eulerian or longer trail
-- statement:
--   Lema de extensión: todo trail, o bien da lugar a un circuito euleriano, o bien se extiende
--   a un trail estrictamente más largo.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L86-L114
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean#L86-L114

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

theorem SimpleGraph.exists_isEulerian_or_longer_trail (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    (∃ w, ∃ q : G.Walk w w, q.IsEulerian) ∨
      ∃ a b, ∃ q : G.Walk a b, q.IsTrail ∧ p.length < q.length := by sorry
