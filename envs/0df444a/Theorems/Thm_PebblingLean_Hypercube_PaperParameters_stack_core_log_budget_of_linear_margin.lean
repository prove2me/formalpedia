-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_core_log_budget_of_linear_margin
-- name    : PebblingLean.Hypercube.PaperParameters.stack_core_log_budget_of_linear_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:46.454657+00:00
-- url     : https://prove2.me/theorems/46b69b57-8dfa-4f4e-ba88-3851f7ad28d1
-- title:
--   Paper Parameters: stack core log budget of linear margin
-- statement:
--   Corrected coarse sufficient condition for the stack core log budget.  It
--   keeps the paired linear margin
--   `a*(log(4/3)-log 2/3)` before using `a≥3n/4`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1224-L1249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1224-L1249

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

theorem PebblingLean.Hypercube.PaperParameters.stack_core_log_budget_of_linear_margin {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n)
    (ha_lower : (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ))
    (hcoarse :
      Real.log 2 + 2 * Real.log (n : ℝ) +
          (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
            Real.log 2 ≤
        (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
            Real.log 2 +
          ((3 : ℝ) * (n : ℝ) / 4) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    Real.log 2 + 2 * Real.log (n : ℝ) +
        (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
          Real.log 2 ≤
      ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
        (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3) := by sorry
