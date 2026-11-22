-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidth_real_ge_of_core_ge
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidth_real_ge_of_core_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:48.507334+00:00
-- url     : https://prove2.me/theorems/f61dca8a-3dd5-4093-a6aa-d5961ae47faa
-- title:
--   Paper Parameters: annulus Width real ge of core ge
-- statement:
--   The Paper Parameters construction uses the annulus Width real ge of core ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L132-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L132-L135

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidth_real_ge_of_core_ge {A K : ℝ} {n : ℕ}
    (hcore : 9 ≤ annulusWidthCore A K n) :
    9 ≤ (annulusWidth A K n : ℝ) := by sorry
