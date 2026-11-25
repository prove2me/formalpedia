-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_exists_isNClique_of_card_nonadj_le
-- name    : SimpleGraph.Reservoir.exists_isNClique_of_card_nonadj_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:27.981582+00:00
-- url     : https://prove2.me/theorems/e0d6c16e-c29c-531c-96de-6113da887f4c
-- title:
--   Reservoir: exists is NClique of card nonadj le
-- statement:
--   **Greedy clique.** Suppose every vertex of the pool has at most `d` non-neighbours in the pool
--   (counting itself). If `j * d < #pool`, then `j` pivots are possible, so the pool contains a
--   `(j + 1)`-clique, and `G` contains a `(#spine + j + 1)`-clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L230-L251
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L230-L251

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
variable (R : G.Reservoir)

theorem SimpleGraph.Reservoir.exists_isNClique_of_card_nonadj_le [DecidableRel G.Adj] {d : ℕ}
    (hd : ∀ v ∈ R.pool, #{w ∈ R.pool | ¬G.Adj v w} ≤ d) (j : ℕ) (hj : j * d < #R.pool) :
    ∃ s, G.IsNClique (#R.spine + (j + 1)) s := by sorry
