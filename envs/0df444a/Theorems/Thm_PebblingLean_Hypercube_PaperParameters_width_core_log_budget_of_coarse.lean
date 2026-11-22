-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_core_log_budget_of_coarse
-- name    : PebblingLean.Hypercube.PaperParameters.width_core_log_budget_of_coarse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:56:50.936746+00:00
-- url     : https://prove2.me/theorems/00989977-b596-46bf-a0e5-b4766d9398b5
-- title:
--   Paper Parameters: width core log budget of coarse
-- statement:
--   Coarse sufficient condition for the Bernstein-width core log budget.  This
--   is the form where every remaining term is expressed using only `n`, `K`, and
--   `A`, up to the standard `sqrt(3n log n)` envelope.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1076-L1116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1076-L1116

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

theorem PebblingLean.Hypercube.PaperParameters.width_core_log_budget_of_coarse {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n)
    (hcoarse :
      Real.log 128 + (2 *
          (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
          Real.log 2 +
          Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
        -4 * Real.log (n : ℝ) +
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
            Real.log 2) :
    Real.log 128 + (2 * (annulusWidthCore A K n + 1)) * Real.log 2 +
        Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      -4 * Real.log (n : ℝ) +
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 := by sorry
