-- Prove2me | Theorems.Thm_SimpleGraph_goodman_sq
-- name    : SimpleGraph.goodman_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:30:52.456164+00:00
-- url     : https://prove2.me/theorems/9b8c11f3-1bb0-41e4-aec8-ef03f598e1d0
-- title:
--   Simple Graph: goodman sq
-- statement:
--   **Goodman's formula with degree imbalance.**
--   `8 (T(G) + T(Gᶜ)) + n (n - 1) ^ 2 = 8 C(n, 3) + ∑ v, (deg_G v - deg_{Gᶜ} v) ^ 2`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L398-L402
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L398-L402

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

theorem SimpleGraph.goodman_sq :
    8 * ((#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) : ℕ) : ℤ) +
        Fintype.card V * ((Fintype.card V : ℤ) - 1) ^ 2 =
      8 * (Fintype.card V).choose 3 + ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by sorry
