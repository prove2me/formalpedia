-- Prove2me | Theorems.Thm_SimpleGraph_isClique_compl_fromEdgeSet_iff
-- name    : SimpleGraph.isClique_compl_fromEdgeSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:59:53.377431+00:00
-- url     : https://prove2.me/theorems/2529f680-359a-4a0f-af0e-44a5775a74e9
-- title:
--   Simple Graph: is Clique compl from Edge Set iff
-- statement:
--   A set `s` is independent in `fromEdgeSet A` exactly when no pair of `s` lies in `A`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L119-L131
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L119-L131

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

theorem SimpleGraph.isClique_compl_fromEdgeSet_iff {A : Finset (Sym2 V)} {s : Finset V} :
    (fromEdgeSet (A : Set (Sym2 V)))ᶜ.IsClique (s : Set V) ↔ Disjoint s.pairs A := by sorry
