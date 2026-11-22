-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_logWidth_of_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.logWidth_of_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:13.913969+00:00
-- url     : https://prove2.me/theorems/c25b5a49-c429-4310-95e2-08badaa73e66
-- title:
--   Paper Parameters: log Width of mul le
-- statement:
--   Multiplication-form sufficient condition for the Bernstein width
--   threshold.  This avoids carrying a division in the remaining asymptotic
--   estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1941-L1954
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1941-L1954

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

theorem PebblingLean.Hypercube.PaperParameters.logWidth_of_mul_le {A K : ℝ} {n : ℕ}
    (hmul :
      128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
          (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
        (loss n) ^ 2 * (minPile (splitM K n) : ℝ)) :
    ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
      (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
        (128 * (2 ^ (2 * annulusWidth A K n) : ℝ)) := by sorry
