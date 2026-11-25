-- Prove2me | Theorems.Thm_SimpleGraph_exists_cliqueFree_of_sq_le_two_pow
-- name    : SimpleGraph.exists_cliqueFree_of_sq_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:48.501871+00:00
-- url     : https://prove2.me/theorems/fab39021-2efc-5878-a5bd-5042976c7202
-- title:
--   Simple Graph: exists clique Free of sq le two pow
-- statement:
--   **Erdős's lower bound** `R(k, k) > 2 ^ (k / 2)`. If `k ≥ 3` and `n ^ 2 ≤ 2 ^ k`, some graph on
--   `n` vertices has neither a `k`-clique nor an independent `k`-set.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L255-L303
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L255-L303

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

theorem SimpleGraph.exists_cliqueFree_of_sq_le_two_pow {k : ℕ} (hk : 3 ≤ k)
    (hn : Fintype.card V ^ 2 ≤ 2 ^ k) :
    ∃ G : SimpleGraph V, G.CliqueFree k ∧ Gᶜ.CliqueFree k := by sorry
