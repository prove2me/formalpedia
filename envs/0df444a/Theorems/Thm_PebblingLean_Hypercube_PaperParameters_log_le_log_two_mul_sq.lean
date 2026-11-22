-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_le_log_two_mul_sq
-- name    : PebblingLean.Hypercube.PaperParameters.log_le_log_two_mul_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:58:31.479914+00:00
-- url     : https://prove2.me/theorems/07d996d8-aadd-47a3-8a62-7db02356a7ed
-- title:
--   Paper Parameters: log le log two mul sq
-- statement:
--   For `n≥1`, the logarithm used in the annulus width dominates `log n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L557-L564
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L557-L564

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

theorem PebblingLean.Hypercube.PaperParameters.log_le_log_two_mul_sq {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ) ^ 2) := by sorry
