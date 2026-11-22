-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_lt_of_four_mul_le
-- name    : PebblingLean.Hypercube.PaperParameters.splitM_lt_of_four_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:40.439728+00:00
-- url     : https://prove2.me/theorems/52b231da-ce01-42a4-93ef-d09fd26d70fe
-- title:
--   Paper Parameters: split M lt of four mul le
-- statement:
--   The Paper Parameters construction uses the split M lt of four mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L351-L356
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L351-L356

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

theorem PebblingLean.Hypercube.PaperParameters.splitM_lt_of_four_mul_le {K : ℝ} {n0 n : ℕ}
    (hn0_pos : 0 < n0) (hn : n0 ≤ n)
    (hquarter : 4 * splitM K n ≤ n) :
    splitM K n < n := by sorry
