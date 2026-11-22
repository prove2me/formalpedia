-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_n_div_two_le_splitA_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.n_div_two_le_splitA_of_four_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:58:09.937613+00:00
-- url     : https://prove2.me/theorems/57c55354-a07e-4a63-9245-73b85b9fe61a
-- title:
--   Paper Parameters: n div two le split A of four mul le
-- statement:
--   A weaker but integer-valued form useful for monotonicity of natural powers:
--   under `4m≤n`, the large factor has dimension at least `n/2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L345-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L345-L349

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

theorem PebblingLean.Hypercube.PaperParameters.n_div_two_le_splitA_of_four_mul_le {K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    n / 2 ≤ splitA K n := by sorry
