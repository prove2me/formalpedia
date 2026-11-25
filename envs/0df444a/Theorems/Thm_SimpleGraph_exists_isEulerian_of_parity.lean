-- Prove2me | Theorems.Thm_SimpleGraph_exists_isEulerian_of_parity
-- name    : SimpleGraph.exists_isEulerian_of_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:33:56.920129+00:00
-- url     : https://prove2.me/theorems/c7627ab0-f518-4ba2-9951-93daf2df8f11
-- title:
--   Simple Graph: exists is Eulerian of parity
-- statement:
--   **Euler (suficiencia, versión con extremos).** Si `G` es conexo y los vértices de grado
--   impar son exactamente `a` y `b` (o no hay ninguno, cuando `a = b`), existe un trail euleriano
--   de `a` a `b`.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L124-L167
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L124-L167

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.exists_isEulerian_of_parity (hconn : G.Connected) {a b : V}
    (h : ∀ x, Even (G.degree x) ↔ (a ≠ b → x ≠ a ∧ x ≠ b)) :
    ∃ p : G.Walk a b, p.IsEulerian := by sorry
