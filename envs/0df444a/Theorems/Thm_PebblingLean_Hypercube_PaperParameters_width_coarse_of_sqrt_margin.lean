-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_coarse_of_sqrt_margin
-- name    : PebblingLean.Hypercube.PaperParameters.width_coarse_of_sqrt_margin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:59:49.781054+00:00
-- url     : https://prove2.me/theorems/4eef49b4-9274-43a5-a7e4-fb5dd1097d0e
-- title:
--   Paper Parameters: width coarse of sqrt margin
-- statement:
--   Coefficient form of the width coarse estimate.  The only growing term on
--   the right is now `sqrt(n log n)` with coefficient
--   `(K/5-2A sqrt 3) log 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1261-L1277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1261-L1277

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

theorem PebblingLean.Hypercube.PaperParameters.width_coarse_of_sqrt_margin {A K : ℝ} {n : ℕ}
    (hmargin :
      Real.log 128 + 3 * Real.log 2 +
          Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
          4 * Real.log (n : ℝ) ≤
        ((K / 5 - 2 * A * Real.sqrt 3) * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + (2 *
        (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
        Real.log 2 +
        Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      -4 * Real.log (n : ℝ) +
        (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
          Real.log 2 := by sorry
