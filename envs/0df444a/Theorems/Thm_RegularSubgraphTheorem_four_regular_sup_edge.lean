-- Prove2me | Theorems.Thm_RegularSubgraphTheorem_four_regular_sup_edge
-- name    : RegularSubgraphTheorem.four_regular_sup_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:39:51.484799+00:00
-- url     : https://prove2.me/theorems/3cd7bdb3-6e94-4121-a142-cadd8bd65592
-- title:
--   Regular Subgraph Theorem: four regular sup edge
-- statement:
--   **Every 4-regular graph plus an edge contains a 3-regular subgraph** (Alon–Friedland–Kalai).
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/Solution.lean#L42-L46
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/Solution.lean#L42-L46

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
public import Definitions.Def_RegularSubgraphs_Solution
public import Theorems.Thm_RegularSubgraph_four_regular_sup_edge

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open RegularSubgraphTheorem
variable {V : Type*} [Fintype V]

theorem RegularSubgraphTheorem.four_regular_sup_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 4) {u w : V} (huw : u ≠ w) (hn : ¬ G.Adj u w) :
    ∃ H : SimpleGraph V, H ≤ G ⊔ edge u w ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = 3 := by sorry
