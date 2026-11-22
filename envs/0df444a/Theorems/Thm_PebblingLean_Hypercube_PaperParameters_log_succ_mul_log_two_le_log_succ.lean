-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_succ_mul_log_two_le_log_succ
-- name    : PebblingLean.Hypercube.PaperParameters.log_succ_mul_log_two_le_log_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:59:56.549316+00:00
-- url     : https://prove2.me/theorems/d7872024-b2db-4e8d-bfe3-4a94bdc4c572
-- title:
--   Paper Parameters: log succ mul log two le log succ
-- statement:
--   Since `log 2≤1`, the factor `log 2` inside
--   `log((n+1)log 2)` can be discarded.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1358-L1373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1358-L1373

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

theorem PebblingLean.Hypercube.PaperParameters.log_succ_mul_log_two_le_log_succ {n : ℕ} :
    Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      Real.log (((n + 1 : ℕ) : ℝ)) := by sorry
