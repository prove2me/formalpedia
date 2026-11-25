-- Prove2me | Theorems.Thm_SimpleGraph_exists_dependentRandomChoice
-- name    : SimpleGraph.exists_dependentRandomChoice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:37.473806+00:00
-- url     : https://prove2.me/theorems/49336a1f-be0f-552b-b554-40285e02d894
-- title:
--   Simple Graph: exists dependent Random Choice
-- statement:
--   **Dependent random choice.** If `r ≥ 1` and `a n ^ t + C(n, r) m ^ t ≤ ∑ v, deg v ^ t`, there
--   is a set `W` of at least `a` vertices in which every `r`-subset has at least `m` common
--   neighbours.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L141-L173
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L141-L173

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

theorem SimpleGraph.exists_dependentRandomChoice [Nonempty V] {t r m a : ℕ} (hr : 1 ≤ r)
    (h : a * Fintype.card V ^ t + (Fintype.card V).choose r * m ^ t ≤ ∑ v, G.degree v ^ t) :
    ∃ W : Finset V, a ≤ #W ∧ ∀ S ⊆ W, #S = r → m ≤ #{u | ∀ v ∈ S, G.Adj v u} := by sorry
