-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_normalizedCost_le_finiteBaseNormalizedBound_of_lt
-- name    : PebblingLean.Hypercube.normalizedCost_le_finiteBaseNormalizedBound_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:39.305255+00:00
-- url     : https://prove2.me/theorems/05993e48-da91-4a00-9b10-3690208d7290
-- title:
--   Hypercube: normalized Cost le finite Base Normalized Bound of lt
-- statement:
--   The Hypercube construction uses the normalized Cost le finite Base Normalized Bound of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L397-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L397-L403

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube

theorem PebblingLean.Hypercube.normalizedCost_le_finiteBaseNormalizedBound_of_lt
    (costBound : ℕ → ℕ) {n0 n : ℕ} (hn : n < n0) :
    normalizedCost costBound n ≤ finiteBaseNormalizedBound costBound n0 := by sorry
