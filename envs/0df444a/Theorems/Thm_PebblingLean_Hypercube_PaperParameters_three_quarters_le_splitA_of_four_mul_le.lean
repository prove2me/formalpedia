-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_quarters_le_splitA_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.three_quarters_le_splitA_of_four_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:55:59.291394+00:00
-- url     : https://prove2.me/theorems/71a615ba-741f-4952-a23d-44bba592bf48
-- title:
--   Paper Parameters: three quarters le split A of four mul le
-- statement:
--   The split condition forces the large factor to contain at least
--   three quarters of the coordinates, as a real inequality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L331-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L331-L341

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

theorem PebblingLean.Hypercube.PaperParameters.three_quarters_le_splitA_of_four_mul_le {K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ) := by sorry
