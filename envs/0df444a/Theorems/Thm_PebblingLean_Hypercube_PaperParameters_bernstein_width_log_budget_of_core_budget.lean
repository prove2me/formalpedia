-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_bernstein_width_log_budget_of_core_budget
-- name    : PebblingLean.Hypercube.PaperParameters.bernstein_width_log_budget_of_core_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:31.243305+00:00
-- url     : https://prove2.me/theorems/4b26eb2f-60d5-43de-98e5-7230a483f887
-- title:
--   Paper Parameters: bernstein width log budget of core budget
-- statement:
--   The Bernstein-width log budget can be proved using the real width core
--   with one unit of ceiling overhead.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1007-L1031
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1007-L1031

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

theorem PebblingLean.Hypercube.PaperParameters.bernstein_width_log_budget_of_core_budget {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A)
    (hcoreBudget :
      Real.log 128 + (2 * (annulusWidthCore A K n + 1)) * Real.log 2 +
          Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
        -4 * Real.log (n : ℝ) +
          ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2) :
    Real.log 128 + ((2 * annulusWidth A K n : ℕ) : ℝ) * Real.log 2 +
        Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      -4 * Real.log (n : ℝ) +
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 := by sorry
