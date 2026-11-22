-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_step
-- name    : PebblingLean.Hypercube.PaperParameters.recursiveCostBound_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:27.757416+00:00
-- url     : https://prove2.me/theorems/f706554d-30ba-435e-bf28-a81617f828fb
-- title:
--   Paper Parameters: recursive Cost Bound step
-- statement:
--   The Paper Parameters construction uses the recursive Cost Bound step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L238-L243
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L238-L243

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

theorem PebblingLean.Hypercube.PaperParameters.recursiveCostBound_step {K : ℝ} {n0 n : ℕ}
    (hn : n0 ≤ n) (hsmall : splitM K n < n) :
    recursiveCostBound K n0 n =
      recursiveCostBound K n0 (splitM K n) * costMultiplier K n := by sorry
