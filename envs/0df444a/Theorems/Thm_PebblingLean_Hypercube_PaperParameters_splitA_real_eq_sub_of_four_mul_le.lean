-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_real_eq_sub_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.splitA_real_eq_sub_of_four_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:09.621784+00:00
-- url     : https://prove2.me/theorems/3048b0d7-07b7-4b2d-93d7-ccc4abf4f907
-- title:
--   Paper Parameters: split A real eq sub of four mul le
-- statement:
--   Real form of the identity `a = n-m` under the split condition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L322-L327
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L322-L327

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

theorem PebblingLean.Hypercube.PaperParameters.splitA_real_eq_sub_of_four_mul_le {K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    (splitA K n : ℝ) = (n : ℝ) - (splitM K n : ℝ) := by sorry
