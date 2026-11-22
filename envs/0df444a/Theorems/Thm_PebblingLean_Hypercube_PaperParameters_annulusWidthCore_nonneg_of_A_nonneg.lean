-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_nonneg_of_A_nonneg
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidthCore_nonneg_of_A_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:32.78725+00:00
-- url     : https://prove2.me/theorems/3db31a28-f043-4919-991a-bd7cf005718c
-- title:
--   Paper Parameters: annulus Width Core nonneg of A nonneg
-- statement:
--   The Paper Parameters construction uses the annulus Width Core nonneg of A nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L109-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L109-L113

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidthCore_nonneg_of_A_nonneg {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) :
    0 ≤ annulusWidthCore A K n := by sorry
