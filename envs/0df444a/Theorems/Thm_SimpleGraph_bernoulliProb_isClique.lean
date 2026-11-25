-- Prove2me | Theorems.Thm_SimpleGraph_bernoulliProb_isClique
-- name    : SimpleGraph.bernoulliProb_isClique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:58.107938+00:00
-- url     : https://prove2.me/theorems/20c5365c-bbd8-4ed1-9390-e4f98b4a57d2
-- title:
--   Simple Graph: bernoulli Prob is Clique
-- statement:
--   A fixed set `s` is a clique of `G(n, p)` with probability `p ^ C(|s|, 2)`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L136-L139
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L136-L139

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

theorem SimpleGraph.bernoulliProb_isClique (s : Finset V) :
    (possibleEdges V).bernoulliProb p (s.pairs ⊆ ·) = p ^ (#s).choose 2 := by sorry
