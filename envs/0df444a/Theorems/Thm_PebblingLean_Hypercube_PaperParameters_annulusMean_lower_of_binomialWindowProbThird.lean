-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusMean_lower_of_binomialWindowProbThird
-- name    : PebblingLean.Hypercube.PaperParameters.annulusMean_lower_of_binomialWindowProbThird
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:13.602793+00:00
-- url     : https://prove2.me/theorems/028689df-5f75-4566-8f36-7cdabe590a5a
-- title:
--   Paper Parameters: annulus Mean lower of binomial Window Prob Third
-- statement:
--   A lower bound for the `Binomial(n,1/3)` mass of the annulus window is
--   exactly the annulus-mean lower bound used by the upper-bound recurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1958-L1974
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1958-L1974

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

theorem PebblingLean.Hypercube.PaperParameters.annulusMean_lower_of_binomialWindowProbThird
    {n rIn rOut : ℕ} {alpha : ℝ}
    (hprob : alpha ≤ binomialWindowProbThird n rIn rOut) :
    alpha * (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) ≤
      (annulusMean n rIn rOut : ℝ) := by sorry
