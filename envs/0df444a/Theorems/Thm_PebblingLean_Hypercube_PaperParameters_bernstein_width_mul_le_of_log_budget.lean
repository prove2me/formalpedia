-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_bernstein_width_mul_le_of_log_budget
-- name    : PebblingLean.Hypercube.PaperParameters.bernstein_width_mul_le_of_log_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:06.969822+00:00
-- url     : https://prove2.me/theorems/1e49d7cf-a82e-4aed-9253-e360d7884c04
-- title:
--   Paper Parameters: bernstein width mul le of log budget
-- statement:
--   Logarithmic sufficient condition for the multiplication-form Bernstein
--   width threshold.  This is the log form of
--   `128 * 2^(2w) * ((a+1)log 2) ≤ loss(n)^2 * 2^(m/5)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L948-L1003
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L948-L1003

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

theorem PebblingLean.Hypercube.PaperParameters.bernstein_width_mul_le_of_log_budget {A K : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hlog :
      Real.log 128 + ((2 * annulusWidth A K n : ℕ) : ℝ) * Real.log 2 +
          Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
        -4 * Real.log (n : ℝ) +
          ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2) :
    128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
        (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
      (loss n) ^ 2 * (minPile (splitM K n) : ℝ) := by sorry
