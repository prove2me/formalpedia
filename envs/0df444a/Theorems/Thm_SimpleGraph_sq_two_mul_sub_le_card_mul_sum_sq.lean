-- Prove2me | Theorems.Thm_SimpleGraph_sq_two_mul_sub_le_card_mul_sum_sq
-- name    : SimpleGraph.sq_two_mul_sub_le_card_mul_sum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:42:18.306058+00:00
-- url     : https://prove2.me/theorems/ec05ca56-c77a-4c85-a5ea-fb5da43cb35a
-- title:
--   Simple Graph: sq two mul sub le card mul sum sq
-- statement:
--   **Edge balance.** `(2 (e(G) - e(Gᶜ))) ^ 2 ≤ n ∑ v, (deg_G v - deg_{Gᶜ} v) ^ 2`: if the red and
--   blue degrees are nearly equal at every vertex, so are the numbers of red and blue edges.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L528-L541
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Goodman.lean#L528-L541

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

theorem SimpleGraph.sq_two_mul_sub_le_card_mul_sum_sq :
    (2 * ((#G.edgeFinset : ℤ) - #Gᶜ.edgeFinset)) ^ 2 ≤
      Fintype.card V * ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by sorry
