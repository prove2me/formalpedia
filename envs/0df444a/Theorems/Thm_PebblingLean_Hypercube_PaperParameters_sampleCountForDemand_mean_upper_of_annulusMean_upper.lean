-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sampleCountForDemand_mean_upper_of_annulusMean_upper
-- name    : PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_mean_upper_of_annulusMean_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:51.406915+00:00
-- url     : https://prove2.me/theorems/03094b4d-3f74-4e78-838c-41ca6511a509
-- title:
--   Paper Parameters: sample Count For Demand mean upper of annulus Mean upper
-- statement:
--   The sampled annulus mean is at most `2t` once the annulus mean is bounded
--   by the full weighted mean and the sample-count ceiling is paid for by the
--   stack-size threshold.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1787-L1867
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1787-L1867

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

theorem PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_mean_upper_of_annulusMean_upper
    {A K : ℝ} {n t : ℕ}
    (hloss : loss n ≤ 1)
    (hannulus_upper :
      (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
        (2 ^ rOut A K n : ℝ) * (((3 : ℝ) / 4) ^ splitA K n))
    (hstack :
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)) :
    (sampleCountForDemand A K n t : ℝ) *
      (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
        2 * (t : ℝ) := by sorry
