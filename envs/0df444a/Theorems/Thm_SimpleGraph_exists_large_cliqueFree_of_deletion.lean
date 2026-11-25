-- Prove2me | Theorems.Thm_SimpleGraph_exists_large_cliqueFree_of_deletion
-- name    : SimpleGraph.exists_large_cliqueFree_of_deletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:43.951947+00:00
-- url     : https://prove2.me/theorems/69dacc20-6aff-5f96-a64d-c5af2f775e1f
-- title:
--   Simple Graph: exists large clique Free of deletion
-- statement:
--   **The deletion method.** For `0 ≤ p ≤ 1`, some graph on `V` has a vertex set `t` of size at
--   least `n - C(n, k) p ^ C(k, 2) - C(n, l) (1 - p) ^ C(l, 2)` containing no `k`-clique and no
--   independent `l`-set, provided `k, l ≥ 1`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L174-L210
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean#L174-L210

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

theorem SimpleGraph.exists_large_cliqueFree_of_deletion (h0 : 0 ≤ p) (h1 : p ≤ 1) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    ∃ (G : SimpleGraph V) (t : Finset V),
      (Fintype.card V : ℝ) - ((Fintype.card V).choose k * p ^ k.choose 2 +
        (Fintype.card V).choose l * (1 - p) ^ l.choose 2) ≤ #t ∧
      (∀ s ⊆ t, ¬G.IsNClique k s) ∧ ∀ s ⊆ t, ¬Gᶜ.IsNClique l s := by sorry
