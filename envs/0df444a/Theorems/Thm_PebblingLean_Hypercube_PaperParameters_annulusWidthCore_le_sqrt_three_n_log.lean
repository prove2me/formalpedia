-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_sqrt_three_n_log
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidthCore_le_sqrt_three_n_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:57.653358+00:00
-- url     : https://prove2.me/theorems/a6b866cc-9afb-4922-adbc-e9c664003fd6
-- title:
--   Paper Parameters: annulus Width Core le sqrt three n log
-- statement:
--   Coarse real upper bound for the annulus-width core.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L530-L554
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L530-L554

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidthCore_le_sqrt_three_n_log {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n) :
    annulusWidthCore A K n ≤
      A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) := by sorry
