-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_two_mul_sq_le_three_log
-- name    : PebblingLean.Hypercube.PaperParameters.log_two_mul_sq_le_three_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:41.294614+00:00
-- url     : https://prove2.me/theorems/bbeff639-7034-404c-9270-8bb926243459
-- title:
--   Paper Parameters: log two mul sq le three log
-- statement:
--   For `n≥2`, `log(2n^2)` is bounded by `3 log n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L515-L527
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L515-L527

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

theorem PebblingLean.Hypercube.PaperParameters.log_two_mul_sq_le_three_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log (2 * (n : ℝ) ^ 2) ≤ 3 * Real.log (n : ℝ) := by sorry
