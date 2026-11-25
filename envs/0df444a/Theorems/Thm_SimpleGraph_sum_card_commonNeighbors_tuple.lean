-- Prove2me | Theorems.Thm_SimpleGraph_sum_card_commonNeighbors_tuple
-- name    : SimpleGraph.sum_card_commonNeighbors_tuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:32.858866+00:00
-- url     : https://prove2.me/theorems/e6587aeb-da69-5026-a940-83111c4acb60
-- title:
--   Simple Graph: sum card common Neighbors tuple
-- statement:
--   Summing the size of the common neighbourhood of a `t`-tuple over all tuples gives
--   `∑ v, deg v ^ t`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L102-L110
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L102-L110

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
omit [DecidableEq V]

theorem SimpleGraph.sum_card_commonNeighbors_tuple (t : ℕ) :
    ∑ τ : Fin t → V, #{v | ∀ i, G.Adj (τ i) v} = ∑ v, G.degree v ^ t := by sorry
