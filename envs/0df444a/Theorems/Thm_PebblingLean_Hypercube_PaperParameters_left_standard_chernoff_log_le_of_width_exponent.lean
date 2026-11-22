-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_left_standard_chernoff_log_le_of_width_exponent
-- name    : PebblingLean.Hypercube.PaperParameters.left_standard_chernoff_log_le_of_width_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:24.170798+00:00
-- url     : https://prove2.me/theorems/1e824b4f-f6a6-4a62-8d2e-dd1b86880026
-- title:
--   Paper Parameters: left standard chernoff log le of width exponent
-- statement:
--   Left-tail standard-lambda log estimate for the annulus window.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3579-L3604
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3579-L3604

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

theorem PebblingLean.Hypercube.PaperParameters.left_standard_chernoff_log_le_of_width_exponent
    {A K : ℝ} {n : ℕ} {E : ℝ}
    (hcenter : annulusWidth A K n ≤ splitA K n / 3)
    (hlam_le_one : annulusChernoffLambda A K n ≤ 1)
    (hE :
      E ≤ (5 / 6) *
        ((annulusWidth A K n : ℝ) ^ 2 / ((splitA K n : ℝ) + 1))) :
    annulusChernoffLambda A K n * (rIn A K n : ℝ) +
        (splitA K n : ℝ) *
          Real.log (((1 : ℝ) / 3) *
              Real.exp (-(annulusChernoffLambda A K n)) +
            ((2 : ℝ) / 3)) ≤ -E := by sorry
