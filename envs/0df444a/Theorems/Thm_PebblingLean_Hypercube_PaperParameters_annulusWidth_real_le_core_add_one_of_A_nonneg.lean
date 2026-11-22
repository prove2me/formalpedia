-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidth_real_le_core_add_one_of_A_nonneg
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidth_real_le_core_add_one_of_A_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:26.113347+00:00
-- url     : https://prove2.me/theorems/37eb93a4-608d-4af3-953f-a26f0400f3d5
-- title:
--   Paper Parameters: annulus Width real le core add one of A nonneg
-- statement:
--   The Paper Parameters construction uses the annulus Width real le core add one of A nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L176-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L176-L180

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidth_real_le_core_add_one_of_A_nonneg {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) :
    (annulusWidth A K n : ℝ) ≤ annulusWidthCore A K n + 1 := by sorry
