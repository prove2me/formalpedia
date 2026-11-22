-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_n_div_five_le_rOut_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.n_div_five_le_rOut_of_four_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:57.530782+00:00
-- url     : https://prove2.me/theorems/758ccc3a-52b7-468d-a5e9-81a208210a21
-- title:
--   Paper Parameters: n div five le r Out of four mul le
-- statement:
--   The Paper Parameters construction uses the n div five le r Out of four mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L201-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L201-L207

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

theorem PebblingLean.Hypercube.PaperParameters.n_div_five_le_rOut_of_four_mul_le {A K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    n / 5 ≤ rOut A K n := by sorry
