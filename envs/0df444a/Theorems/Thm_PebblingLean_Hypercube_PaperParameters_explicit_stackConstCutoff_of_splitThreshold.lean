-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_stackConstCutoff_of_splitThreshold
-- name    : PebblingLean.Hypercube.PaperParameters.explicit_stackConstCutoff_of_splitThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:28.633157+00:00
-- url     : https://prove2.me/theorems/fdb9f6b2-6c33-40db-9359-0b7e249d966a
-- title:
--   Paper Parameters: explicit stack Const Cutoff of split Threshold
-- statement:
--   The stack constant cutoff follows from the explicit split cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5690-L5707
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5690-L5707

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

theorem PebblingLean.Hypercube.PaperParameters.explicit_stackConstCutoff_of_splitThreshold {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    12 * Real.log 2 ≤
      (n0 : ℝ) * (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by sorry
