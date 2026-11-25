-- Prove2me | Theorems.Thm_RegularSubgraph_totalDegree_poly_le
-- name    : RegularSubgraph.totalDegree_poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:21.804242+00:00
-- url     : https://prove2.me/theorems/9178601f-0b08-4d85-908b-1972bfc8de01
-- title:
--   Regular Subgraph: total Degree poly le
-- statement:
--   The Regular Subgraph construction uses the total Degree poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L76-L86
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L76-L86

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
variable {G p}
variable [hp : Fact p.Prime]

theorem RegularSubgraph.totalDegree_poly_le (v : V) : (poly G p v).totalDegree ≤ p - 1 := by sorry
