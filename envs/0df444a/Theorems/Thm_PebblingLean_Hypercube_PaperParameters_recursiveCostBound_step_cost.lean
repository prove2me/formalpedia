-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_step_cost
-- name    : PebblingLean.Hypercube.PaperParameters.recursiveCostBound_step_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:09.458504+00:00
-- url     : https://prove2.me/theorems/e6c93980-2fe3-4980-8edc-3b329c5a76b1
-- title:
--   Paper Parameters: recursive Cost Bound step cost
-- statement:
--   The Paper Parameters construction uses the recursive Cost Bound step cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L686-L694
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L686-L694

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

theorem PebblingLean.Hypercube.PaperParameters.recursiveCostBound_step_cost {K : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter : ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n) :
    ∀ n : ℕ, n0 ≤ n →
      recursiveCostBound K n0 (splitM K n) * costMultiplier K n ≤
        recursiveCostBound K n0 n := by sorry
