-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_sq_eq
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidthCore_sq_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:58:49.033444+00:00
-- url     : https://prove2.me/theorems/f0a51a63-f3d6-4cc0-bc0d-ab20cd545983
-- title:
--   Paper Parameters: annulus Width Core sq eq
-- statement:
--   The Paper Parameters construction uses the annulus Width Core sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L566-L579
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L566-L579

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidthCore_sq_eq {A K : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (annulusWidthCore A K n) ^ 2 =
      A ^ 2 * ((splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2)) := by sorry
