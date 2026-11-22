-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_le_sqrt_n_log
-- name    : PebblingLean.Hypercube.PaperParameters.log_le_sqrt_n_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:02.026874+00:00
-- url     : https://prove2.me/theorems/04be27f9-cbc0-4d21-b7e6-6d9c7f1db9eb
-- title:
--   Paper Parameters: log le sqrt n log
-- statement:
--   The elementary comparison `log n≤sqrt(n log n)` for `n≥1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1433-L1450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1433-L1450

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

theorem PebblingLean.Hypercube.PaperParameters.log_le_sqrt_n_log {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤
      Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by sorry
