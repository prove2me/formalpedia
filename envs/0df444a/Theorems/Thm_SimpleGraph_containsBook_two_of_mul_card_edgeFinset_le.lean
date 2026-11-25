-- Prove2me | Theorems.Thm_SimpleGraph_containsBook_two_of_mul_card_edgeFinset_le
-- name    : SimpleGraph.containsBook_two_of_mul_card_edgeFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:57.412677+00:00
-- url     : https://prove2.me/theorems/d570c6f0-710b-51b5-a883-5f6f39f3da0c
-- title:
--   Simple Graph: contains Book two of mul card edge Finset le
-- statement:
--   **Books from triangles.** If `t · e ≤ 3 · T`, where `e` is the number of edges and `T` the
--   number of triangles, then some edge spans a book with `t` pages.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L246-L251
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L246-L251

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

theorem SimpleGraph.containsBook_two_of_mul_card_edgeFinset_le [DecidableEq V] {t : ℕ}
    (hE : G.edgeFinset.Nonempty) (h : t * #G.edgeFinset ≤ 3 * #(G.cliqueFinset 3)) :
    G.ContainsBook 2 t := by sorry
