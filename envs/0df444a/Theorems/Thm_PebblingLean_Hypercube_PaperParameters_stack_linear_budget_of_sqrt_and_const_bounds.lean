-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_budget_of_sqrt_and_const_bounds
-- name    : PebblingLean.Hypercube.PaperParameters.stack_linear_budget_of_sqrt_and_const_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:29.138214+00:00
-- url     : https://prove2.me/theorems/37645e44-f2c9-47d6-9d2d-3518c8e9705f
-- title:
--   Paper Parameters: stack linear budget of sqrt and const bounds
-- statement:
--   Large-`n` sufficient conditions for the residual stack budget.  The first
--   condition pays for `2 log n`; the second pays for `3 log 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1624-L1657
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1624-L1657

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

theorem PebblingLean.Hypercube.PaperParameters.stack_linear_budget_of_sqrt_and_const_bounds {n : ℕ}
    (hn : 1 ≤ n)
    (hsqrt :
      4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (n : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3))
    (hconst :
      12 * Real.log 2 ≤
        (n : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
      ((3 : ℝ) * (n : ℝ) / 4) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by sorry
