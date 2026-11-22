-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_sqrt_budget_of_log_linear_margin_sq
-- name    : PebblingLean.Hypercube.PaperParameters.stack_sqrt_budget_of_log_linear_margin_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:35.087806+00:00
-- url     : https://prove2.me/theorems/8245ffe1-94ea-4ac8-86e1-f1c48e575f61
-- title:
--   Paper Parameters: stack sqrt budget of log linear margin sq
-- statement:
--   Squared sufficient condition for the stack square-root budget.  With
--   `c = log(4/3)-log(2)/3`, the condition `16 log n≤n c^2` implies
--   `4 sqrt(n log n)≤n c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1683-L1721
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1683-L1721

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters

theorem PebblingLean.Hypercube.PaperParameters.stack_sqrt_budget_of_log_linear_margin_sq {n : ℕ}
    (hlog :
      16 * Real.log (n : ℝ) ≤
        (n : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) ^ 2) :
    4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (n : ℝ) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by sorry
