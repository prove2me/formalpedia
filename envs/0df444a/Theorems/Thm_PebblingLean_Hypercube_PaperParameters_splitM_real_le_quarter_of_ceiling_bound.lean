-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_real_le_quarter_of_ceiling_bound
-- name    : PebblingLean.Hypercube.PaperParameters.splitM_real_le_quarter_of_ceiling_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:31.043819+00:00
-- url     : https://prove2.me/theorems/babb1fab-46ef-41cf-b512-ed216d0cd1a1
-- title:
--   Paper Parameters: split M real le quarter of ceiling bound
-- statement:
--   To prove the real split estimate, it is enough to bound the expression
--   inside the ceiling with one unit of ceiling overhead.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L370-L379
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L370-L379

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

theorem PebblingLean.Hypercube.PaperParameters.splitM_real_le_quarter_of_ceiling_bound {K : ℝ} {n : ℕ}
    (hnonneg : 0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hbound :
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤ (n : ℝ) / 4) :
    (splitM K n : ℝ) ≤ (n : ℝ) / 4 := by sorry
