-- Prove2me | Theorems.Thm_RegularSubgraph_exists_regular_subgraph
-- name    : RegularSubgraph.exists_regular_subgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:24.950077+00:00
-- url     : https://prove2.me/theorems/65e988a6-ced1-58a9-8d89-fb4a1e0623df
-- title:
--   Regular Subgraph: exists regular subgraph
-- statement:
--   **Alon–Friedland–Kalai (1984), prime case.** A graph with maximum degree at most `2p − 1` and
--   average degree greater than `2p − 2` has a nonempty subgraph in which every degree is `0` or `p`.
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L102-L184
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L102-L184

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]

theorem RegularSubgraph.exists_regular_subgraph (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : p.Prime)
    (hmax : ∀ v, G.degree v ≤ 2 * p - 1)
    (havg : (2 * p - 2) * Fintype.card V < 2 * #G.edgeFinset) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = p := by sorry
