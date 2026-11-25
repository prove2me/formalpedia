-- Prove2me | Theorems.Thm_SimpleGraph_sum_card_bad_le
-- name    : SimpleGraph.sum_card_bad_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:38.214888+00:00
-- url     : https://prove2.me/theorems/f6af248c-06fb-4a5d-97d7-a20bf172b99e
-- title:
--   Simple Graph: sum card bad le
-- statement:
--   Summing the number of `r`-sets with fewer than `m` common neighbours that lie in the common
--   neighbourhood of a `t`-tuple gives at most `C(n, r) m ^ t`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L114-L136
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L114-L136

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

theorem SimpleGraph.sum_card_bad_le (t r m : ℕ) :
    ∑ τ : Fin t → V, #{S ∈ (univ : Finset V).powersetCard r |
        #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v} ≤
      (Fintype.card V).choose r * m ^ t := by sorry
