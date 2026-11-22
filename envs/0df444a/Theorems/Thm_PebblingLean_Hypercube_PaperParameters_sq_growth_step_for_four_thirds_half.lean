-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sq_growth_step_for_four_thirds_half
-- name    : PebblingLean.Hypercube.PaperParameters.sq_growth_step_for_four_thirds_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:00.603846+00:00
-- url     : https://prove2.me/theorems/b9891b67-cb72-4352-bcec-1bb90bf5866a
-- title:
--   Paper Parameters: sq growth step for four thirds half
-- statement:
--   Two-step growth estimate used to prove that `(4/3)^(n/2)` eventually
--   dominates `n^2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2022-L2026
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2022-L2026

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

theorem PebblingLean.Hypercube.PaperParameters.sq_growth_step_for_four_thirds_half (n : ℕ) (hn : 14 ≤ n) :
    ((n + 2 : ℕ) : ℝ) ^ 2 ≤ ((4 : ℝ) / 3) * (n : ℝ) ^ 2 := by sorry
