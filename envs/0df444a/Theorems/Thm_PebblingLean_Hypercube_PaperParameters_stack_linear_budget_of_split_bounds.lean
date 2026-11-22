-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_budget_of_split_bounds
-- name    : PebblingLean.Hypercube.PaperParameters.stack_linear_budget_of_split_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:01.615566+00:00
-- url     : https://prove2.me/theorems/2d8a25ce-e159-4884-b3b1-6f1ba72c3bfb
-- title:
--   Paper Parameters: stack linear budget of split bounds
-- statement:
--   Split form of the residual stack budget: one inequality pays for
--   `2 log n`, and the other pays for the constant `3 log 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1418-L1430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1418-L1430

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

theorem PebblingLean.Hypercube.PaperParameters.stack_linear_budget_of_split_bounds {n : ℕ}
    (hlog :
      2 * Real.log (n : ℝ) ≤
        ((n : ℝ) / 2) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3))
    (hconst :
      3 * Real.log 2 ≤
        ((n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
      ((3 : ℝ) * (n : ℝ) / 4) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by sorry
