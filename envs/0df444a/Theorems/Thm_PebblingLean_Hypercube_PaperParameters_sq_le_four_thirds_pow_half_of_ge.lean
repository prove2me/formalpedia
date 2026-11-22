-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sq_le_four_thirds_pow_half_of_ge
-- name    : PebblingLean.Hypercube.PaperParameters.sq_le_four_thirds_pow_half_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:14.405004+00:00
-- url     : https://prove2.me/theorems/6c02df07-e85f-4e23-9dc9-b1f3ddedfae5
-- title:
--   Paper Parameters: sq le four thirds pow half of ge
-- statement:
--   Explicit elementary growth threshold:
--   for `n≥58`, `(4/3)^(⌊n/2⌋)` dominates `n^2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2030-L2048
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2030-L2048

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

theorem PebblingLean.Hypercube.PaperParameters.sq_le_four_thirds_pow_half_of_ge (n : ℕ) (hn : 58 ≤ n) :
    (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ (n / 2)) := by sorry
