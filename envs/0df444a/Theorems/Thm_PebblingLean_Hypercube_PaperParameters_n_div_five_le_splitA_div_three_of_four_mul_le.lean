-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_n_div_five_le_splitA_div_three_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.n_div_five_le_splitA_div_three_of_four_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:56.7989+00:00
-- url     : https://prove2.me/theorems/6f35ff66-0aa4-4e57-850a-b2737c84d05a
-- title:
--   Paper Parameters: n div five le split A div three of four mul le
-- statement:
--   The coarse split condition `4m≤n` already makes the center radius
--   large enough for the recursive pile invariant `2^(n/5)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L195-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L195-L199

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

theorem PebblingLean.Hypercube.PaperParameters.n_div_five_le_splitA_div_three_of_four_mul_le {K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    n / 5 ≤ splitA K n / 3 := by sorry
