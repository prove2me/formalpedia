-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sampleCountForDemand_fiberCost
-- name    : PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_fiberCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:43.72774+00:00
-- url     : https://prove2.me/theorems/160e9f5a-8782-4138-ad6a-ae7c07b63db4
-- title:
--   Paper Parameters: sample Count For Demand fiber Cost
-- statement:
--   The sample-count ceiling still fits inside the integer fiber multiplier
--   once the annulus stack size is at most the reserved half-loss budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L709-L759
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L709-L759

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

theorem PebblingLean.Hypercube.PaperParameters.sampleCountForDemand_fiberCost {A K : ℝ} {n t : ℕ}
    (hstack :
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)) :
    sampleCountForDemand A K n t * 2 ^ rOut A K n ≤
      t * costMultiplier K n := by sorry
