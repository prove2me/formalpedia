-- Prove2me | Theorems.Thm_RegularSubgraph_four_regular_sup_edge
-- name    : RegularSubgraph.four_regular_sup_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:34.518979+00:00
-- url     : https://prove2.me/theorems/c89cd277-7960-54fa-ac1a-37cb8f0107c1
-- title:
--   Regular Subgraph: four regular sup edge
-- statement:
--   **Every 4-regular graph plus an edge contains a 3-regular subgraph** (Alon–Friedland–Kalai).
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L188-L217
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L188-L217

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]

theorem RegularSubgraph.four_regular_sup_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 4) {u w : V} (huw : u ≠ w) (hn : ¬ G.Adj u w) :
    ∃ H : SimpleGraph V, H ≤ G ⊔ edge u w ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = 3 := by sorry
