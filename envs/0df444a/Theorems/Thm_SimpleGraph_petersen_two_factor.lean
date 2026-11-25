-- Prove2me | Theorems.Thm_SimpleGraph_petersen_two_factor
-- name    : SimpleGraph.petersen_two_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:42:59.874605+00:00
-- url     : https://prove2.me/theorems/72ab8acc-defa-4835-80f3-321c2e24afa0
-- title:
--   Simple Graph: petersen two factor
-- statement:
--   **Teorema del 2-factor de Petersen.** Todo grafo finito `2k`-regular se descompone en `k`
--   2-factores disjuntos en aristas.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean#L177-L285
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean#L177-L285

module
public import Definitions.Def_Euler_Orientation
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Set.Card
public import Definitions.Def_Euler_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.petersen_two_factor (k : ℕ) (h : ∀ v, G.degree v = 2 * k) :
    ∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G) ∧
      (∀ i v, ((F i).neighborSet v).ncard = 2) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ ⨆ i, F i = G := by sorry
