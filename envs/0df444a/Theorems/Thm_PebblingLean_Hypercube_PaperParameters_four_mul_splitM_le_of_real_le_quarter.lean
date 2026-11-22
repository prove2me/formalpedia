-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_four_mul_splitM_le_of_real_le_quarter
-- name    : PebblingLean.Hypercube.PaperParameters.four_mul_splitM_le_of_real_le_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:37.73303+00:00
-- url     : https://prove2.me/theorems/a9ddd2a7-023c-4e44-95cf-7b18caa6b325
-- title:
--   Paper Parameters: four mul split M le of real le quarter
-- statement:
--   Real-valued sufficient condition for the split estimate.  This is the
--   form produced by asymptotic bounds for `ceil(K sqrt(n log n))`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L360-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L360-L366

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

theorem PebblingLean.Hypercube.PaperParameters.four_mul_splitM_le_of_real_le_quarter {K : ℝ} {n : ℕ}
    (hreal : (splitM K n : ℝ) ≤ (n : ℝ) / 4) :
    4 * splitM K n ≤ n := by sorry
