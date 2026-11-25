-- Prove2me | Theorems.Thm_SimpleGraph_exists_adj_four_mul_card_edgeFinset_le
-- name    : SimpleGraph.exists_adj_four_mul_card_edgeFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:14.019171+00:00
-- url     : https://prove2.me/theorems/45d3bc9f-c26d-46fe-8b6c-4653c43f1158
-- title:
--   Simple Graph: exists adj four mul card edge Finset le
-- statement:
--   **Books from edge density.** If `G` has `e > 0` edges on `n` vertices, some edge `uv` satisfies
--   `4e ≤ n · (codeg(u, v) + n)`: it spans a book with at least `4e/n - n` pages.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L280-L302
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L280-L302

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

theorem SimpleGraph.exists_adj_four_mul_card_edgeFinset_le (hE : G.edgeFinset.Nonempty) :
    ∃ u v, G.Adj u v ∧
      4 * #G.edgeFinset ≤ Fintype.card V * (Fintype.card (G.commonNeighbors u v) +
        Fintype.card V) := by sorry
