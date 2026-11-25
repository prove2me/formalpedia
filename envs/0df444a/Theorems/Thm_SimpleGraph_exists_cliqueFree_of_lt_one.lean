-- Prove2me | Theorems.Thm_SimpleGraph_exists_cliqueFree_of_lt_one
-- name    : SimpleGraph.exists_cliqueFree_of_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:00:53.817496+00:00
-- url     : https://prove2.me/theorems/3044debc-5056-4c97-966c-6f037a37ec0a
-- title:
--   Simple Graph: exists clique Free of lt one
-- statement:
--   **The biased first-moment bound.** If `0 ≤ p ≤ 1` and
--   `C(n, k) p ^ C(k, 2) + C(n, l) (1 - p) ^ C(l, 2) < 1`, some graph on `n` vertices has no `k`-clique
--   and no independent `l`-set.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L216-L241
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L216-L241

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
omit [DecidableEq V]

theorem SimpleGraph.exists_cliqueFree_of_lt_one (h0 : 0 ≤ p) (h1 : p ≤ 1) {k l : ℕ}
    (h : (Fintype.card V).choose k * p ^ k.choose 2 +
      (Fintype.card V).choose l * (1 - p) ^ l.choose 2 < 1) :
    ∃ G : SimpleGraph V, G.CliqueFree k ∧ Gᶜ.CliqueFree l := by sorry
