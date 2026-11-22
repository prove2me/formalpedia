-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_widthConstCutoff_of_splitThreshold
-- name    : PebblingLean.Hypercube.PaperParameters.explicit_widthConstCutoff_of_splitThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:26.866395+00:00
-- url     : https://prove2.me/theorems/1e436521-38d2-4d31-ab90-bc1687de735b
-- title:
--   Paper Parameters: explicit width Const Cutoff of split Threshold
-- statement:
--   For `K=217`, the width constant cutoff follows from the split cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5640-L5666
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5640-L5666

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

theorem PebblingLean.Hypercube.PaperParameters.explicit_widthConstCutoff_of_splitThreshold {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    Real.log 128 + 4 * Real.log 2 ≤
      ((217 : ℝ) / 30 * Real.log 2) *
        Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) := by sorry
