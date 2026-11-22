-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_minPile_le_stackSize_of_exponent_le
-- name    : PebblingLean.Hypercube.PaperParameters.minPile_le_stackSize_of_exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:15.493029+00:00
-- url     : https://prove2.me/theorems/a882111f-a276-436c-b18b-8706455ab970
-- title:
--   Paper Parameters: min Pile le stack Size of exponent le
-- statement:
--   The Paper Parameters construction uses the min Pile le stack Size of exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L696-L699
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L696-L699

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

theorem PebblingLean.Hypercube.PaperParameters.minPile_le_stackSize_of_exponent_le {A K : ℝ} {n : ℕ}
    (h : n / 5 ≤ rOut A K n) :
    minPile n ≤ 2 ^ rOut A K n := by sorry
