-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rOut_sub_rIn_le_two_width
-- name    : PebblingLean.Hypercube.PaperParameters.rOut_sub_rIn_le_two_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:57.385086+00:00
-- url     : https://prove2.me/theorems/e3d6a40a-ff7c-4ba6-bf46-57264a75fdcc
-- title:
--   Paper Parameters: r Out sub r In le two width
-- statement:
--   The annulus diameter is at most twice the half-width parameter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L210-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L210-L213

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

theorem PebblingLean.Hypercube.PaperParameters.rOut_sub_rIn_le_two_width {A K : ℝ} {n : ℕ} :
    rOut A K n - rIn A K n ≤ 2 * annulusWidth A K n := by sorry
