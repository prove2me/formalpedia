-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_logMin_of_widthBound
-- name    : PebblingLean.Hypercube.PaperParameters.logMin_of_widthBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:00.309806+00:00
-- url     : https://prove2.me/theorems/5ad901f6-5682-437b-9b5e-646f09af2539
-- title:
--   Paper Parameters: log Min of width Bound
-- statement:
--   It is enough to prove the minimum-demand Bernstein threshold with
--   `2^(2w)`, where `w` is the annulus half-width, since
--   `rOut-rIn ≤ 2w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1910-L1936
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1910-L1936

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

theorem PebblingLean.Hypercube.PaperParameters.logMin_of_widthBound {A K : ℝ} {n : ℕ}
    (hwidthLog :
      ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
          (128 * (2 ^ (2 * annulusWidth A K n) : ℝ))) :
    ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
      (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
        (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ)) := by sorry
