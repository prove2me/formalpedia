-- Prove2me | Theorems.Thm_RegularSubgraph_adj_of_val_ne_zero
-- name    : RegularSubgraph.adj_of_val_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:03.771991+00:00
-- url     : https://prove2.me/theorems/f22919ac-351b-4865-86e2-39bf3b5f41c1
-- title:
--   Regular Subgraph: adj of val ne zero
-- statement:
--   The Regular Subgraph construction uses the adj of val ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L64-L67
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L64-L67

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
omit [Fintype V]

theorem RegularSubgraph.adj_of_val_ne_zero {x : Edge G → ZMod p} {a b : V} (h : val G p x a b ≠ 0) :
    G.Adj a b := by sorry
