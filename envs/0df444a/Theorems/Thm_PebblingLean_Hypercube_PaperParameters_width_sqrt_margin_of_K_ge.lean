-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_sqrt_margin_of_K_ge
-- name    : PebblingLean.Hypercube.PaperParameters.width_sqrt_margin_of_K_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:59:59.314732+00:00
-- url     : https://prove2.me/theorems/5381b3da-8826-4e41-ad9a-4b0aa49010ab
-- title:
--   Paper Parameters: width sqrt margin of K ge
-- statement:
--   A simple constant-domination sufficient condition for the width sqrt
--   margin.  The stronger but convenient assumption `15A√3≤K` leaves a positive
--   coefficient `K/15` for the residual logarithmic terms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1301-L1323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1301-L1323

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

theorem PebblingLean.Hypercube.PaperParameters.width_sqrt_margin_of_K_ge {A K : ℝ} {n : ℕ}
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hbudget :
      Real.log 128 + 3 * Real.log 2 +
          Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
          4 * Real.log (n : ℝ) ≤
        (K / 15 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + 3 * Real.log 2 +
        Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
        4 * Real.log (n : ℝ) ≤
      ((K / 5 - 2 * A * Real.sqrt 3) * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by sorry
