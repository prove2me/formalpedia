-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_finalAnalyticBudgets_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_finalAnalyticBudgets_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:16.756219+00:00
-- url     : https://prove2.me/theorems/c9384d4c-e2db-4d0d-bf94-a4ee250ceaaa
-- title:
--   Paper Parameters: has Real Upper Bound of Kdom final Analytic Budgets finite Base
-- statement:
--   Final analytic-budget wrapper before choosing explicit numerical
--   constants.  The non-Chernoff deterministic thresholds remain finite cutoff
--   checks, while the annulus Chernoff hypotheses are reduced to:
--
--   * a coarse upper bound making the annulus width fit inside `a/3`;
--   * one cutoff check implying `core≥9` thereafter;
--   * the constant inequality `A^2≥16`, which gives the six-log Chernoff exponent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5331-L5415
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5331-L5415

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_finalAnalyticBudgets_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hA_sq : 16 ≤ A ^ 2)
    (hthreeCoreCoarse :
      ∀ n : ℕ, n0 ≤ n →
        3 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) ≤
          (3 : ℝ) * (n : ℝ) / 4)
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
