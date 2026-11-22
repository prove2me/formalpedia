-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_lossProduct
-- name    : PebblingLean.Hypercube.LossRecurrence.cost_le_lossProduct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:55:24.424802+00:00
-- url     : https://prove2.me/theorems/a9f220b5-7ad5-41ac-bb96-3a3ba1c644fc
-- title:
--   Loss Recurrence: cost le loss Product
-- statement:
--   Iterating a normalized recurrence gives a finite product of the losses
--   times the terminal normalized cost.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L67-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L67-L98

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

theorem PebblingLean.Hypercube.LossRecurrence.cost_le_lossProduct
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (k n : ℕ) (hactive : ActiveFor next n0 k n) :
    R n ≤ lossProduct next loss k n * R (iterate next k n) := by sorry
