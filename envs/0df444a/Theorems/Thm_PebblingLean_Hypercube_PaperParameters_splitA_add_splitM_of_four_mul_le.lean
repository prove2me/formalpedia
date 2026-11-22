-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_add_splitM_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.splitA_add_splitM_of_four_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:28.243934+00:00
-- url     : https://prove2.me/theorems/2395687c-38dd-4f96-9642-2f21a50f3f8b
-- title:
--   Paper Parameters: split A add split M of four mul le
-- statement:
--   The Paper Parameters construction uses the split A add split M of four mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L314-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L314-L319

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

theorem PebblingLean.Hypercube.PaperParameters.splitA_add_splitM_of_four_mul_le {K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    splitA K n + splitM K n = n := by sorry
