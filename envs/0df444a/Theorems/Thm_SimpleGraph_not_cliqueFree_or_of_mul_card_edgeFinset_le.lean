-- Prove2me | Theorems.Thm_SimpleGraph_not_cliqueFree_or_of_mul_card_edgeFinset_le
-- name    : SimpleGraph.not_cliqueFree_or_of_mul_card_edgeFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:32:54.587593+00:00
-- url     : https://prove2.me/theorems/0adf6669-d6a7-4e99-b9e0-8b3926570959
-- title:
--   Simple Graph: not clique Free or of mul card edge Finset le
-- statement:
--   **Book forcing from triangle density.** If `G` has no `(r + 2)`-clique, at least one edge, and
--   `t · e ≤ 3 · T` (with `e` edges and `T` triangles), then `RamseyBound t r s` gives an independent
--   set of size `s`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L317-L320
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L317-L320

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

theorem SimpleGraph.not_cliqueFree_or_of_mul_card_edgeFinset_le [DecidableEq V] {t r s : ℕ}
    (hE : G.edgeFinset.Nonempty) (h : t * #G.edgeFinset ≤ 3 * #(G.cliqueFinset 3))
    (hR : RamseyBound t r s) : ¬G.CliqueFree (r + 2) ∨ ¬Gᶜ.CliqueFree s := by sorry
