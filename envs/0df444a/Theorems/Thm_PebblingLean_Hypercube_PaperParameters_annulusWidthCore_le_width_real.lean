-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_width_real
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidthCore_le_width_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:23.727031+00:00
-- url     : https://prove2.me/theorems/885f58d6-87a1-4a48-a70d-2a297df32101
-- title:
--   Paper Parameters: annulus Width Core le width real
-- statement:
--   The integer annulus width dominates its real core because it is a ceiling.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L126-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L126-L130

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidthCore_le_width_real {A K : ℝ} {n : ℕ} :
    annulusWidthCore A K n ≤ (annulusWidth A K n : ℝ) := by sorry
