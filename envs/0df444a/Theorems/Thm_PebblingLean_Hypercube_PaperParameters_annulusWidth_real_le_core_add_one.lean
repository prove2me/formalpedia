-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidth_real_le_core_add_one
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidth_real_le_core_add_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:56:21.486351+00:00
-- url     : https://prove2.me/theorems/9c088cb1-9748-4c6a-b95b-22a9bb6b37ed
-- title:
--   Paper Parameters: annulus Width real le core add one
-- statement:
--   The Paper Parameters construction uses the annulus Width real le core add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L120-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L120-L123

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidth_real_le_core_add_one {A K : ℝ} {n : ℕ}
    (hcore : 0 ≤ annulusWidthCore A K n) :
    (annulusWidth A K n : ℝ) ≤ annulusWidthCore A K n + 1 := by sorry
