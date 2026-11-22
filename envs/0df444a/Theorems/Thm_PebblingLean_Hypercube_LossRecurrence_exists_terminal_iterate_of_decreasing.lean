-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_exists_terminal_iterate_of_decreasing
-- name    : PebblingLean.Hypercube.LossRecurrence.exists_terminal_iterate_of_decreasing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:00.790246+00:00
-- url     : https://prove2.me/theorems/76a200af-a8ce-451a-ae59-dad79692e960
-- title:
--   Loss Recurrence: exists terminal iterate of decreasing
-- statement:
--   A strictly decreasing dimension map always reaches the finite base range
--   after finitely many recursive steps.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L180-L190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L180-L190

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence

theorem PebblingLean.Hypercube.LossRecurrence.exists_terminal_iterate_of_decreasing
    {next : ℕ → ℕ} {n0 : ℕ}
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n) (n : ℕ) :
    ∃ k : ℕ, ActiveFor next n0 k n ∧ iterate next k n < n0 := by sorry
