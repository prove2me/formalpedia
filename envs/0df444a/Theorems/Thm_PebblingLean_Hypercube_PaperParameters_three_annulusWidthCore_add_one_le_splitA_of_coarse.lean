-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_annulusWidthCore_add_one_le_splitA_of_coarse
-- name    : PebblingLean.Hypercube.PaperParameters.three_annulusWidthCore_add_one_le_splitA_of_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:41.304319+00:00
-- url     : https://prove2.me/theorems/866a6c16-5c6c-42f4-8442-59d58e586382
-- title:
--   Paper Parameters: three annulus Width Core add one le split A of coarse
-- statement:
--   A coarse upper estimate sufficient for the center-width condition
--   `3(core+1)≤a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L599-L614
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L599-L614

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

theorem PebblingLean.Hypercube.PaperParameters.three_annulusWidthCore_add_one_le_splitA_of_coarse
    {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n)
    (ha_lower : (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ))
    (hcoarse :
      3 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) ≤
        (3 : ℝ) * (n : ℝ) / 4) :
    3 * (annulusWidthCore A K n + 1) ≤ (splitA K n : ℝ) := by sorry
