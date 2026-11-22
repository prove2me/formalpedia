-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_uniform_bound_of_decreasing_lossBound
-- name    : PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_decreasing_lossBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:06:39.26098+00:00
-- url     : https://prove2.me/theorems/d361e220-27e6-4e2d-ac2d-f76935400850
-- title:
--   Loss Recurrence: cost uniform bound of decreasing loss Bound
-- statement:
--   Uniform normalized-cost bound for a decreasing dimension map, assuming a
--   separate estimate on every terminal loss sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L354-L374
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L354-L374

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

theorem PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_decreasing_lossBound
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B L : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hlossSum :
      ∀ n k : ℕ, ActiveFor next n0 k n →
        iterate next k n < n0 → lossSum next loss k n ≤ L)
    (n : ℕ) :
    R n ≤ Real.exp L * B := by sorry
