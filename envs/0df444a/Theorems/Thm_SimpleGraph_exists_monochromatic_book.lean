-- Prove2me | Theorems.Thm_SimpleGraph_exists_monochromatic_book
-- name    : SimpleGraph.exists_monochromatic_book
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:41:57.807842+00:00
-- url     : https://prove2.me/theorems/2cab5260-63fa-514c-9247-bc8d5fde8d33
-- title:
--   Simple Graph: exists monochromatic book
-- statement:
--   **Monochromatic books.** If `4q + 2 ≤ n`, every red/blue colouring of `K_n` has an edge whose
--   endpoints have at least `q` common neighbours in the colour of that edge. For `q = 1` this is the
--   monochromatic triangle in `K_6`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L482-L522
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L482-L522

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype V]

theorem SimpleGraph.exists_monochromatic_book {q : ℕ} (hq : 4 * q + 2 ≤ Fintype.card V) :
    ∃ u v, (G.Adj u v ∧ q ≤ Fintype.card (G.commonNeighbors u v)) ∨
      (Gᶜ.Adj u v ∧ q ≤ Fintype.card (Gᶜ.commonNeighbors u v)) := by sorry
