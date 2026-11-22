-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_uniform_bound_of_geometric_loss_le_two
-- name    : PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_geometric_loss_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:36.030485+00:00
-- url     : https://prove2.me/theorems/928aba8f-69d0-4fb8-9a98-5edcd9e812ec
-- title:
--   Loss Recurrence: cost uniform bound of geometric loss le two
-- statement:
--   Convenient geometric-loss bound for ratio at most `1/2`, giving total
--   loss at most `2M`.  The paper's recursion has a much smaller ratio (`1/16`)
--   after increasing the base threshold, so this intentionally uses a relaxed
--   constant.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L309-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L309-L328

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

theorem PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_geometric_loss_le_two
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B q M : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hq_half : q ≤ (1 : ℝ) / 2)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M) (n : ℕ) :
    R n ≤ Real.exp (2 * M) * B := by sorry
