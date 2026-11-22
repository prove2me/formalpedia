-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_ge_nine_of_coarse_sq
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidthCore_ge_nine_of_coarse_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:58:32.428806+00:00
-- url     : https://prove2.me/theorems/dccb8299-7084-4e13-b095-c6ae199d4730
-- title:
--   Paper Parameters: annulus Width Core ge nine of coarse sq
-- statement:
--   The coarse square budget for `core≥9` propagates from a lower bound on
--   `a` and `log(2n^2)≥log n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L618-L644
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L618-L644

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidthCore_ge_nine_of_coarse_sq
    {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 1 ≤ n)
    (ha_lower : (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ))
    (hbudget :
      81 ≤ A ^ 2 * (((3 : ℝ) * (n : ℝ) / 4) *
        Real.log (n : ℝ))) :
    9 ≤ annulusWidthCore A K n := by sorry
