-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rOut_real_le_div_three_add_widthCore_add_one_of_A_nonneg
-- name    : PebblingLean.Hypercube.PaperParameters.rOut_real_le_div_three_add_widthCore_add_one_of_A_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:54.174161+00:00
-- url     : https://prove2.me/theorems/20cfdfe5-61f0-42b7-b32f-b20157246b17
-- title:
--   Paper Parameters: r Out real le div three add width Core add one of A nonneg
-- statement:
--   The Paper Parameters construction uses the r Out real le div three add width Core add one of A nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L182-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L182-L191

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

theorem PebblingLean.Hypercube.PaperParameters.rOut_real_le_div_three_add_widthCore_add_one_of_A_nonneg
    {A K : ℝ} {n : ℕ} (hA : 0 ≤ A) :
    (rOut A K n : ℝ) ≤
      ((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1 := by sorry
