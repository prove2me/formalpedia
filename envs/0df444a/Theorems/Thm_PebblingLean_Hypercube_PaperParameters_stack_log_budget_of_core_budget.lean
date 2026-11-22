-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_log_budget_of_core_budget
-- name    : PebblingLean.Hypercube.PaperParameters.stack_log_budget_of_core_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:36.574029+00:00
-- url     : https://prove2.me/theorems/1d7b0d51-b4f9-43a0-aa92-c9dcdfae2da7
-- title:
--   Paper Parameters: stack log budget of core budget
-- statement:
--   The stack log budget can be proved using the real width core with one unit
--   of ceiling overhead in the outer radius.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1035-L1057
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1035-L1057

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

theorem PebblingLean.Hypercube.PaperParameters.stack_log_budget_of_core_budget {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A)
    (hcoreBudget :
      Real.log 2 + 2 * Real.log (n : ℝ) +
          (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
            Real.log 2 ≤
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
          (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3)) :
    Real.log 2 + 2 * Real.log (n : ℝ) +
        (rOut A K n : ℝ) * Real.log 2 ≤
      ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
        (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3) := by sorry
