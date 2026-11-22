-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_succ_le_log_two_add_log
-- name    : PebblingLean.Hypercube.PaperParameters.log_succ_le_log_two_add_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:02.166158+00:00
-- url     : https://prove2.me/theorems/943748c0-7598-46ae-9737-a03d8b6d9253
-- title:
--   Paper Parameters: log succ le log two add log
-- statement:
--   For `n≥1`, `n+1≤2n`, hence `log(n+1)≤log 2+log n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1376-L1389
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1376-L1389

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

theorem PebblingLean.Hypercube.PaperParameters.log_succ_le_log_two_add_log {n : ℕ} (hn : 1 ≤ n) :
    Real.log (((n + 1 : ℕ) : ℝ)) ≤
      Real.log 2 + Real.log (n : ℝ) := by sorry
