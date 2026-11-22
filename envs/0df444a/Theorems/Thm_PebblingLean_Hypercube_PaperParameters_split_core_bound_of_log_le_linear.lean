-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_split_core_bound_of_log_le_linear
-- name    : PebblingLean.Hypercube.PaperParameters.split_core_bound_of_log_le_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:30.477808+00:00
-- url     : https://prove2.me/theorems/c894b816-fe83-476d-9f75-ca83dfa6ca43
-- title:
--   Paper Parameters: split core bound of log le linear
-- statement:
--   A simpler sufficient condition for the ceiling-core split estimate.
--   For large `n`, proving `K^2 log n ≤ n/64` is enough to force
--   `K sqrt(n log n)+1 ≤ n/4`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L389-L426
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L389-L426

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

theorem PebblingLean.Hypercube.PaperParameters.split_core_bound_of_log_le_linear {K : ℝ} {n : ℕ}
    (hK : 0 ≤ K)
    (hn8 : 8 ≤ n)
    (hlogLinear : K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64) :
    K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤
      (n : ℝ) / 4 := by sorry
