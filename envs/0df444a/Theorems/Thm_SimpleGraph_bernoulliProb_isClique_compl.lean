-- Prove2me | Theorems.Thm_SimpleGraph_bernoulliProb_isClique_compl
-- name    : SimpleGraph.bernoulliProb_isClique_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:58.674121+00:00
-- url     : https://prove2.me/theorems/a9024a2b-8d40-4a76-93ef-cd7f594cb174
-- title:
--   Simple Graph: bernoulli Prob is Clique compl
-- statement:
--   A fixed set `s` is independent in `G(n, p)` with probability `(1 - p) ^ C(|s|, 2)`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L142-L145
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L142-L145

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_RandomGraph
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V]
variable [Fintype V] {p : ℝ}

theorem SimpleGraph.bernoulliProb_isClique_compl (s : Finset V) :
    (possibleEdges V).bernoulliProb p (Disjoint · s.pairs) = (1 - p) ^ (#s).choose 2 := by sorry
