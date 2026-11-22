-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sixteen_exp_neg_le_loss_of_log_budget
-- name    : PebblingLean.Hypercube.PaperParameters.sixteen_exp_neg_le_loss_of_log_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:13.131922+00:00
-- url     : https://prove2.me/theorems/d347d9bc-7950-4e6e-bc1d-acb30cdb6c6a
-- title:
--   Paper Parameters: sixteen exp neg le loss of log budget
-- statement:
--   Log-scale sufficient condition for a Chernoff tail budget.  If
--   `E ≥ log 16 + 2 log n`, then `16 exp(-E) ≤ n^{-2}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2052-L2079
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2052-L2079

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

theorem PebblingLean.Hypercube.PaperParameters.sixteen_exp_neg_le_loss_of_log_budget {n : ℕ} {E : ℝ}
    (hn : 0 < n)
    (hlog : Real.log 16 + 2 * Real.log (n : ℝ) ≤ E) :
    16 * Real.exp (-E) ≤ loss n := by sorry
