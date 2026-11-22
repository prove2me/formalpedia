-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_base_cost
-- name    : PebblingLean.Hypercube.PaperParameters.recursiveCostBound_base_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:44.875186+00:00
-- url     : https://prove2.me/theorems/db1b32e1-3fb1-40f7-9cb2-d3421f1d049a
-- title:
--   Paper Parameters: recursive Cost Bound base cost
-- statement:
--   The Paper Parameters construction uses the recursive Cost Bound base cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L245-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L245-L248

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

theorem PebblingLean.Hypercube.PaperParameters.recursiveCostBound_base_cost {K : ℝ} {n0 : ℕ} :
    ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ recursiveCostBound K n0 n := by sorry
