-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_split_log_budget_of_quadratic_threshold
-- name    : PebblingLean.Hypercube.PaperParameters.split_log_budget_of_quadratic_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:17.870535+00:00
-- url     : https://prove2.me/theorems/98986371-915c-4489-806f-878c1d353694
-- title:
--   Paper Parameters: split log budget of quadratic threshold
-- statement:
--   Explicit large-`n` sufficient condition for the split estimate
--   `K^2 log n≤n/64`.  It is intentionally coarse, but isolates this residual
--   analytic input behind a single quadratic threshold.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1455-L1483
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1455-L1483

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

theorem PebblingLean.Hypercube.PaperParameters.split_log_budget_of_quadratic_threshold {K : ℝ} {n : ℕ}
    (hthreshold : (128 * K ^ 2) ^ 2 ≤ (n : ℝ)) :
    K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64 := by sorry
