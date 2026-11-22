-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_cutoffAnalyticBudgets_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_cutoffAnalyticBudgets_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:17.784987+00:00
-- url     : https://prove2.me/theorems/6438f9e8-003d-4498-8ecc-20cf61e16d9f
-- title:
--   Paper Parameters: has Real Upper Bound of Kdom cutoff Analytic Budgets finite Base
-- statement:
--   Cutoff-only annulus analytic wrapper.  Compared with
--   `hasRealUpperBound_of_Kdom_finalAnalyticBudgets_finiteBase`, the remaining
--   coarse width-fit hypothesis has also been collapsed to one quadratic cutoff
--   condition at `n0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5455-L5503
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5455-L5503

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_cutoffAnalyticBudgets_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hA_sq : 16 ≤ A ^ 2)
    (hwidthFitThreshold :
      (128 * (A * Real.sqrt 3) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hcoreNineCutoff :
      81 ≤ A ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
        Real.log (n0 : ℝ)))
    (hwidthConstCutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)))
    (hstackLogThreshold :
      (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
