-- Prove2me | Theorems.Thm_RegularSubgraphTheorem_exists_regular_subgraph
-- name    : RegularSubgraphTheorem.exists_regular_subgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:36:53.331097+00:00
-- url     : https://prove2.me/theorems/3f199f4f-20c4-41d3-bf67-7c0d6a573597
-- title:
--   Regular Subgraph Theorem: exists regular subgraph
-- statement:
--   **Alon–Friedland–Kalai (1984), prime case.** A graph with maximum degree at most `2p − 1` and
--   average degree greater than `2p − 2` has a nonempty subgraph in which every degree is `0` or `p`.
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/Solution.lean#L33-L38
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/Solution.lean#L33-L38

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
public import Definitions.Def_RegularSubgraphs_Solution
public import Theorems.Thm_RegularSubgraph_exists_regular_subgraph

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open RegularSubgraphTheorem
variable {V : Type*} [Fintype V]

theorem RegularSubgraphTheorem.exists_regular_subgraph (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : p.Prime)
    (hmax : ∀ v, G.degree v ≤ 2 * p - 1)
    (havg : (2 * p - 2) * Fintype.card V < 2 * #G.edgeFinset) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = p := by sorry
