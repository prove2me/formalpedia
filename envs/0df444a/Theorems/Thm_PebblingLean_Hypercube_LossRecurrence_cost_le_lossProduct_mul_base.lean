-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_lossProduct_mul_base
-- name    : PebblingLean.Hypercube.LossRecurrence.cost_le_lossProduct_mul_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:20.788812+00:00
-- url     : https://prove2.me/theorems/5342cbab-ae2e-41ba-9cb2-8007569d9ea9
-- title:
--   Loss Recurrence: cost le loss Product mul base
-- statement:
--   Version of `cost_le_lossProduct` with the terminal cost bounded by a
--   specified base constant.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L102-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L102-L113

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

theorem PebblingLean.Hypercube.LossRecurrence.cost_le_lossProduct_mul_base
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 k n : ℕ} {B : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hactive : ActiveFor next n0 k n)
    (hbase : R (iterate next k n) ≤ B) :
    R n ≤ lossProduct next loss k n * B := by sorry
