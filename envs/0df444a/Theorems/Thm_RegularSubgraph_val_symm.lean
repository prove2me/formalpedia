-- Prove2me | Theorems.Thm_RegularSubgraph_val_symm
-- name    : RegularSubgraph.val_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:53.841437+00:00
-- url     : https://prove2.me/theorems/21742db1-6ae6-427f-b99e-9c14454f6389
-- title:
--   Regular Subgraph: val symm
-- statement:
--   The Regular Subgraph construction uses the val symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L54-L61
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L54-L61

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

theorem RegularSubgraph.val_symm (x : Edge G → ZMod p) (a b : V) : val G p x a b = val G p x b a := by sorry
