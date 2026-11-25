-- Prove2me | Theorems.Thm_SimpleGraph_exists_dependentRandomChoice_of_card_edgeFinset
-- name    : SimpleGraph.exists_dependentRandomChoice_of_card_edgeFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:48.306014+00:00
-- url     : https://prove2.me/theorems/fec5f734-94f1-4519-a787-bf736f97a886
-- title:
--   Simple Graph: exists dependent Random Choice of card edge Finset
-- statement:
--   **Dependent random choice, edge-count form** (Fox–Sudakov). Let `d = 2e / n` be the average
--   degree. If `a + C(n, r) (m / n) ^ t ≤ n (d / n) ^ t` and `r ≥ 1`, there is a set `W` of at least
--   `a` vertices in which every `r`-subset has at least `m` common neighbours.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L178-L214
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L178-L214

module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_DependentRandomChoice
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem SimpleGraph.exists_dependentRandomChoice_of_card_edgeFinset [Nonempty V] {t r m a : ℕ} (hr : 1 ≤ r)
    (h : (a : ℝ) + (Fintype.card V).choose r * ((m : ℝ) / Fintype.card V) ^ t ≤
      Fintype.card V * ((2 * #G.edgeFinset : ℝ) / Fintype.card V / Fintype.card V) ^ t) :
    ∃ W : Finset V, a ≤ #W ∧ ∀ S ⊆ W, #S = r → m ≤ #{u | ∀ v ∈ S, G.Adj v u} := by sorry
