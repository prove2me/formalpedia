-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rIn_real_le_third_sub_width
-- name    : PebblingLean.Hypercube.PaperParameters.rIn_real_le_third_sub_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:22.980151+00:00
-- url     : https://prove2.me/theorems/60e49b6d-cd5c-4d96-be8d-5b1c9db80533
-- title:
--   Paper Parameters: r In real le third sub width
-- statement:
--   If the annulus half-width fits inside the center radius, then the inner
--   radius is at most `a/3-w` in real notation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L485-L493
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L485-L493

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

theorem PebblingLean.Hypercube.PaperParameters.rIn_real_le_third_sub_width {A K : ℝ} {n : ℕ}
    (hcenter : annulusWidth A K n ≤ splitA K n / 3) :
    (rIn A K n : ℝ) ≤
      (splitA K n : ℝ) / 3 - (annulusWidth A K n : ℝ) := by sorry
