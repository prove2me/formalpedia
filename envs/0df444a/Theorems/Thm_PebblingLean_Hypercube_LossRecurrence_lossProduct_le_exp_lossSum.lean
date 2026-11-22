-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_lossProduct_le_exp_lossSum
-- name    : PebblingLean.Hypercube.LossRecurrence.lossProduct_le_exp_lossSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:24.411699+00:00
-- url     : https://prove2.me/theorems/dd122aa8-435f-4eee-876b-6610e028efbd
-- title:
--   Loss Recurrence: loss Product le exp loss Sum
-- statement:
--   A finite product of factors `1 + loss` is bounded by the exponential of
--   the corresponding finite sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L117-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L117-L140

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

theorem PebblingLean.Hypercube.LossRecurrence.lossProduct_le_exp_lossSum {next : ℕ → ℕ} {loss : ℕ → ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n) (k n : ℕ) :
    lossProduct next loss k n ≤ Real.exp (lossSum next loss k n) := by sorry
