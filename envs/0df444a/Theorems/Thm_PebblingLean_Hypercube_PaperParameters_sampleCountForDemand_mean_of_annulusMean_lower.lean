-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sampleCountForDemand_mean_of_annulusMean_lower
-- name    : PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_mean_of_annulusMean_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:46.1798+00:00
-- url     : https://prove2.me/theorems/a8fb4d3a-f8f7-4656-b349-072e74d638f6
-- title:
--   Paper Parameters: sample Count For Demand mean of annulus Mean lower
-- statement:
--   The concrete sample count gives the required mean surplus once the annulus
--   mean captures at least a `(1-delta/8)` fraction of the ideal weighted mean.
--   Here `delta = loss n = n^{-2}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L764-L834
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L764-L834

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

theorem PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_mean_of_annulusMean_lower {A K : ℝ} {n t : ℕ}
    (hloss : loss n ≤ 2)
    (hannulus :
      (1 - loss n / 8) * (2 ^ rOut A K n : ℝ) *
          (((3 : ℝ) / 4) ^ splitA K n) ≤
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ)) :
    (t : ℝ) + demandGapForDemand n t ≤
      (sampleCountForDemand A K n t : ℝ) *
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) := by sorry
