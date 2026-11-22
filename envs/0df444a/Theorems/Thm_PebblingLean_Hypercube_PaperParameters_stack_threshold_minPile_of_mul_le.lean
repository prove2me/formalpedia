-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_threshold_minPile_of_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.stack_threshold_minPile_of_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:58:55.335881+00:00
-- url     : https://prove2.me/theorems/d6fde235-0dc4-47a0-882e-4feaeec72c2c
-- title:
--   Paper Parameters: stack threshold min Pile of mul le
-- statement:
--   Multiplication-form sufficient condition for the stack-size threshold.
--   Since `loss n = n^{-2}`, this says the product
--   `minPile(m)(4/3)^a` has room for `2 n^2` copies of the annulus stack size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L873-L895
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L873-L895

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

theorem PebblingLean.Hypercube.PaperParameters.stack_threshold_minPile_of_mul_le {A K : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hmul :
      2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
        (minPile (splitM K n) : ℝ) * (((4 : ℝ) / 3) ^ splitA K n)) :
    (2 ^ rOut A K n : ℝ) ≤
      (loss n / 2) * (minPile (splitM K n) : ℝ) *
        (((4 : ℝ) / 3) ^ splitA K n) := by sorry
