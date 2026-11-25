-- Prove2me | Theorems.Thm_RegularSubgraph_eval_poly
-- name    : RegularSubgraph.eval_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:18.368686+00:00
-- url     : https://prove2.me/theorems/edd235fb-1207-4344-8811-a3bc1447770f
-- title:
--   Regular Subgraph: eval poly
-- statement:
--   The Regular Subgraph construction uses the eval poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L88-L96
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L88-L96

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

theorem RegularSubgraph.eval_poly (x : Edge G → ZMod p) (v : V) :
    eval x (poly G p v) = (#{w | val G p x v w ≠ 0} : ℕ) := by sorry
