-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_uniform_bound_of_terminal_lossBound
-- name    : PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_terminal_lossBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:06:27.526613+00:00
-- url     : https://prove2.me/theorems/b236da85-cce7-487e-92d0-714a92cfbe5c
-- title:
--   Loss Recurrence: cost uniform bound of terminal loss Bound
-- statement:
--   Uniform normalized-cost bound from an explicit terminal path and a bound
--   on the loss accumulated along that path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L332-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L332-L350

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

theorem PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_terminal_lossBound
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B L : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hterminal :
      ∀ n : ℕ, ∃ k : ℕ,
        ActiveFor next n0 k n ∧
          iterate next k n < n0 ∧
            lossSum next loss k n ≤ L)
    (n : ℕ) :
    R n ≤ Real.exp L * B := by sorry
