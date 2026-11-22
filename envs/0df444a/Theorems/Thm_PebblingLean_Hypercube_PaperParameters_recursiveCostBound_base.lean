-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_base
-- name    : PebblingLean.Hypercube.PaperParameters.recursiveCostBound_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:22.628163+00:00
-- url     : https://prove2.me/theorems/6c3a09b0-34c3-42f2-9d97-2662cd55b0d5
-- title:
--   Paper Parameters: recursive Cost Bound base
-- statement:
--   The Paper Parameters construction uses the recursive Cost Bound base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L233-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L233-L236

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

theorem PebblingLean.Hypercube.PaperParameters.recursiveCostBound_base {K : ℝ} {n0 n : ℕ} (hn : n < n0) :
    recursiveCostBound K n0 n = 2 ^ n * minPile n := by sorry
