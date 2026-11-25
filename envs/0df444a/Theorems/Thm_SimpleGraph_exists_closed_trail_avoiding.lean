-- Prove2me | Theorems.Thm_SimpleGraph_exists_closed_trail_avoiding
-- name    : SimpleGraph.exists_closed_trail_avoiding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:34:22.388584+00:00
-- url     : https://prove2.me/theorems/c19ff2d2-9ac2-414a-b824-da1ff83cff79
-- title:
--   Simple Graph: exists closed trail avoiding
-- statement:
--   Sea `S` una lista de aristas que en cada vértice tiene la paridad del grado. Si `x` tiene
--   una arista fuera de `S`, existe un trail cerrado en `x`, de longitud positiva, que no usa
--   aristas de `S`.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L70-L119
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Trail.lean#L70-L119

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.exists_closed_trail_avoiding {S : List (Sym2 V)} (hS : S.Nodup)
    (hSsub : ∀ e ∈ S, e ∈ G.edgeSet)
    (hpar : ∀ y, Even (S.countP fun e => y ∈ e) ↔ Even (G.degree y))
    {x y₀ : V} (hxy : G.Adj x y₀) (hnot : s(x, y₀) ∉ S) :
    ∃ c : G.Walk x x, c.IsTrail ∧ 0 < c.length ∧ ∀ e ∈ c.edges, e ∉ S := by sorry
