-- Prove2me | Theorems.Thm_RegularSubgraph_eval_var
-- name    : RegularSubgraph.eval_var
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:18.151212+00:00
-- url     : https://prove2.me/theorems/9f0c2051-037c-4a7a-91a0-2c9efab33203
-- title:
--   Regular Subgraph: eval var
-- statement:
--   The Regular Subgraph construction uses the eval var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L70-L72
-- source:
--   https://github.com/jtraverso/regular-subgraphs/blob/daea9b30d10bfae6c75ba7be5904080119bbbdba/RegularSubgraphLib/RegularSubgraph.lean#L70-L72

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

theorem RegularSubgraph.eval_var (x : Edge G → ZMod p) (a b : V) : eval x (var G p a b) = val G p x a b := by sorry
