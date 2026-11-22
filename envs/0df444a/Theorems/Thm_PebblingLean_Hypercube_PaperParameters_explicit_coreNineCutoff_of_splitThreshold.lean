-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_coreNineCutoff_of_splitThreshold
-- name    : PebblingLean.Hypercube.PaperParameters.explicit_coreNineCutoff_of_splitThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:16.865509+00:00
-- url     : https://prove2.me/theorems/a09572b5-0986-4347-8746-7decb769dbc9
-- title:
--   Paper Parameters: explicit core Nine Cutoff of split Threshold
-- statement:
--   For `A=4`, the `core≥9` cutoff follows from the split cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5621-L5637
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5621-L5637

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

theorem PebblingLean.Hypercube.PaperParameters.explicit_coreNineCutoff_of_splitThreshold {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    81 ≤ (4 : ℝ) ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
      Real.log (n0 : ℝ)) := by sorry
