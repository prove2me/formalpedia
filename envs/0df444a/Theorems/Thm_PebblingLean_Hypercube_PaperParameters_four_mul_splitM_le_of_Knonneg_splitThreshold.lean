-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_four_mul_splitM_le_of_Knonneg_splitThreshold
-- name    : PebblingLean.Hypercube.PaperParameters.four_mul_splitM_le_of_Knonneg_splitThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:10.875848+00:00
-- url     : https://prove2.me/theorems/45362a1e-0b13-4151-9180-01e09c1c96b9
-- title:
--   Paper Parameters: four mul split M le of Knonneg split Threshold
-- statement:
--   The split estimate derived from the explicit quadratic cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5297-L5321
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5297-L5321

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

theorem PebblingLean.Hypercube.PaperParameters.four_mul_splitM_le_of_Knonneg_splitThreshold
    {K : ℝ} {n0 n : ℕ}
    (hK : 0 ≤ K)
    (hn0_growth : 58 ≤ n0)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hn : n0 ≤ n) :
    4 * splitM K n ≤ n := by sorry
